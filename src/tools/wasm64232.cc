/* Copyright 2022 Alexey Kutepov <reximkut@gmail.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#include <iostream>

#include "src/apply-names.h"
#include "src/binary-reader-ir.h"
#include "src/binary-reader.h"
#include "src/error-formatter.h"
#include "src/feature.h"
#include "src/generate-names.h"
#include "src/ir.h"
#include "src/option-parser.h"
#include "src/stream.h"
#include "src/validator.h"
#include "src/wast-lexer.h"
#include "src/wat-writer.h"
#include "src/cast.h"
#include "src/binary-writer.h"
#include "src/filenames.h"

using namespace wabt;

struct Store {
    Var i32;
    Var i64;
    Var f32;
    Var f64;
};

static int s_verbose;
static std::string s_infile;
static std::string s_outfile;
static std::unique_ptr<FileStream> s_log_stream;
static bool s_read_debug_names = true;
static bool s_fail_on_custom_section_error = true;
static WriteBinaryOptions s_write_binary_options;

static const char s_description[] =
    "Convert wasm64 to wasm32 by converting all pointers accordingly for loads/stores\n"
    "\n"
    "examples:\n"
    "  $ wasm64232 test64.wasm -o test32.wasm\n";

static std::string DefaultOuputName(std::string_view input_name)
{
    // Strip existing extension and add .wasm
    std::string result(StripExtension(GetBasename(input_name)));
    result += ".64232.wasm";
    return result;
}

static void ParseOptions(int argc, char** argv)
{
    OptionParser parser("wasm64232", s_description);

    parser.AddOption('v', "verbose", "Use multiple times for more info", []() {
        s_verbose++;
        s_log_stream = FileStream::CreateStderr();
    });
    parser.AddOption(
        'o', "output", "FILENAME",
        "Output file for the generated wast file, by default use stdout",
    [](const char* argument) {
        s_outfile = argument;
        ConvertBackslashToSlash(&s_outfile);
    });
    parser.AddArgument("filename", OptionParser::ArgumentCount::One,
    [](const char* argument) {
        s_infile = argument;
        ConvertBackslashToSlash(&s_infile);
    });
    parser.Parse(argc, argv);
}

#define UNIMPLEMENTED(message) \
    do { \
        std::cout << __FILE__ << ":" << __LINE__ << ": UNIMPLEMENTED: " << message << "\n"; \
        exit(1); \
    } while (0)
#define UNREACHABLE \
    do { \
        std::cout << __FILE__ << ":" << __LINE__ << ": UNREACHABLE\n"; \
        exit(1); \
    } while (0)


void PatchExprList(ExprList *exprs, Store store)
{
    for (auto it = exprs->begin(); it != exprs->end(); ++it) {
        switch (it->type()) {
        case ExprType::Store: {
            auto store_expr = cast<StoreExpr>(&*it);
            switch (store_expr->opcode) {
            case Opcode::I32Store:
            case Opcode::I32Store8:
            case Opcode::I32Store16:
                exprs->insert(it, MakeUnique<CallExpr>(Var(store.i32)));
                break;

            case Opcode::I64Store:
            case Opcode::I64Store8:
            case Opcode::I64Store16:
            case Opcode::I64Store32:
                exprs->insert(it, MakeUnique<CallExpr>(Var(store.i64)));
                break;

            case Opcode::F32Store:
                exprs->insert(it, MakeUnique<CallExpr>(Var(store.f32)));
                break;

            case Opcode::F64Store:
                exprs->insert(it, MakeUnique<CallExpr>(Var(store.f64)));
                break;

            default:
                std::cout << "Unsupported store instruction " << store_expr->opcode.GetName() << std::endl;
                exit(1);
            }
        }
        break;
        case ExprType::Load:
            exprs->insert(it, MakeUnique<ConvertExpr>(Opcode::I32WrapI64));
            break;
        case ExprType::Block:
            PatchExprList(&cast<BlockExpr>(&*it)->block.exprs, store);
            break;
        case ExprType::Loop:
            PatchExprList(&cast<LoopExpr>(&*it)->block.exprs, store);
            break;
        default:
        {}
        }
    }
}

void PatchFunc(Func *func, Store store)
{
    PatchExprList(&func->exprs, store);
}

Var GenerateWrapStoreForType(Module *module, Type type)
{
    auto type_field = MakeUnique<TypeModuleField>();
    auto func_type = MakeUnique<FuncType>();
    func_type->sig.param_types.push_back(Type(Type::I64));
    func_type->sig.param_types.push_back(type);
    func_type->sig.result_types.push_back(Type(Type::I32));
    func_type->sig.result_types.push_back(type);
    type_field->type = std::move(func_type);
    auto func_type_index = Var(module->types.size());
    module->AppendField(std::move(type_field));

    auto func_field = MakeUnique<FuncModuleField>();
    func_field->func.decl.has_func_type = true;
    func_field->func.decl.type_var = func_type_index;
    func_field->func.exprs.push_back(MakeUnique<LocalGetExpr>(Var(0)));
    func_field->func.exprs.push_back(MakeUnique<ConvertExpr>(Opcode::I32WrapI64));
    func_field->func.exprs.push_back(MakeUnique<LocalGetExpr>(Var(1)));
    auto func_index = Var(module->funcs.size());
    module->AppendField(std::move(func_field));
    return Var(func_index);
}

void PatchInitExprs(ExprList *exprs)
{
    for (auto it = exprs->begin(); it != exprs->end(); it++) {
        switch (it->type()) {
        case ExprType::Const: {
            auto const_expr = cast<ConstExpr>(&*it);
            const_expr->const_.set_u32(const_expr->const_.u32());
            break;
        }
        default:
            UNREACHABLE;
        }
    }
}

int ProgramMain(int argc, char** argv)
{
    InitStdio();
    ParseOptions(argc, argv);

    std::vector<uint8_t> file_data;
    Result result = ReadFile(s_infile.c_str(), &file_data);
    if (Failed(result)) {
        std::cout << "ERROR: could not read file " << s_infile << "\n";
        return 1;
    }

    std::cout << "Read " << file_data.size() << " bytes\n";

    Features features;
    Errors errors;
    const bool kStopOnFirstError = true;
    Module module;
    features.enable_memory64();

    {
        ReadBinaryOptions options(features, s_log_stream.get(),
                                  s_read_debug_names, kStopOnFirstError,
                                  s_fail_on_custom_section_error);
        result = ReadBinaryIr(s_infile.c_str(), file_data.data(), file_data.size(),
                              options, &errors, &module);
    }
    if (Failed(result)) {
        std::cout << "ERROR: could not parse binary data from file " << s_infile << "\n";
        FormatErrorsToFile(errors, Location::Type::Binary);
        return 1;
    }

    result = ValidateModule(&module, &errors, ValidateOptions(features));
    if (Failed(result)) {
        std::cout << "ERROR: validation failed\n";
        FormatErrorsToFile(errors, Location::Type::Binary);
        return 1;
    }

    for (auto memory: module.memories) {
        memory->page_limits.is_64 = false;
    }

    Store store;
    store.i32 = GenerateWrapStoreForType(&module, Type(Type::I32));
    store.i64 = GenerateWrapStoreForType(&module, Type(Type::I64));
    store.f32 = GenerateWrapStoreForType(&module, Type(Type::F32));
    store.f64 = GenerateWrapStoreForType(&module, Type(Type::F64));

    for (auto func: module.funcs) {
        PatchFunc(func, store);
    }

    for (auto data: module.data_segments) {
        PatchInitExprs(&data->offset);
    }

    result = ValidateModule(&module, &errors, ValidateOptions(features));
    if (Failed(result)) {
        std::cout << "ERROR: second validation failed\n";
        FormatErrorsToFile(errors, Location::Type::Binary);
        return 1;
    }

    MemoryStream stream(s_log_stream.get());
    s_write_binary_options.features = features;
    result = WriteBinaryModule(&stream, &module, s_write_binary_options);

    if (Failed(result)) {
        std::cout << "ERROR: could not generate binary data for the patched module" << std::endl;
        FormatErrorsToFile(errors, Location::Type::Binary);
        return 1;
    }

    if (s_outfile.empty()) {
        s_outfile = DefaultOuputName(s_infile);
    }

    stream.output_buffer().WriteToFile(s_outfile);

    return 0;
}

int main(int argc, char **argv)
{
    WABT_TRY
    return ProgramMain(argc, argv);
    WABT_CATCH_BAD_ALLOC_AND_EXIT
}

// Lean compiler output
// Module: Lean.Elab.DocString.Builtin.Parsing
// Imports: public import Lean.Parser.Extension public import Lean.DocString.Syntax public import Init.While import Init.Data.Array.Attach import Init.Data.Array.Mem
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of input"};
static const lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5_value;
static const lean_closure_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__1_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__7_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__3_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__4_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__5_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__8_value),((lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__6_value)}};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Not a quoted string literal"};
static const lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0_value;
static lean_once_cell_t l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__2));
v___x_5_ = lean_unsigned_to_nat(14u);
v___x_6_ = lean_unsigned_to_nat(22u);
v___x_7_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__1));
v___x_8_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__0));
v___x_9_ = l_mkPanicMessageWithDecl(v___x_8_, v___x_7_, v___x_6_, v___x_5_, v___x_4_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(lean_object* v_inst_10_, lean_object* v_s_11_){
_start:
{
lean_object* v___y_13_; lean_object* v___y_14_; lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v___y_29_; lean_object* v___x_34_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = 1;
v___x_34_ = l_Lean_Syntax_getPos_x3f(v_s_11_, v___x_27_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_36_ = l_panic___redArg(v___x_26_, v___x_35_);
v___y_29_ = v___x_36_;
goto v___jp_28_;
}
else
{
lean_object* v_val_37_; 
v_val_37_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v___x_34_, 1);
v___y_29_ = v_val_37_;
goto v___jp_28_;
}
v___jp_12_:
{
lean_object* v_toApplicative_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v_toApplicative_15_ = lean_ctor_get(v_inst_10_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v_inst_10_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v_inst_10_, 1);
lean_dec(v_unused_25_);
v___x_17_ = v_inst_10_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_toApplicative_15_);
lean_dec(v_inst_10_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_toPure_19_; lean_object* v___x_21_; 
v_toPure_19_ = lean_ctor_get(v_toApplicative_15_, 1);
lean_inc(v_toPure_19_);
lean_dec_ref(v_toApplicative_15_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___y_14_);
lean_ctor_set(v___x_17_, 0, v___y_13_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___y_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v___y_14_);
v___x_21_ = v_reuseFailAlloc_23_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
lean_object* v___x_22_; 
v___x_22_ = lean_apply_2(v_toPure_19_, lean_box(0), v___x_21_);
return v___x_22_;
}
}
}
v___jp_28_:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Syntax_getTailPos_x3f(v_s_11_, v___x_27_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_32_ = l_panic___redArg(v___x_26_, v___x_31_);
v___y_13_ = v___y_29_;
v___y_14_ = v___x_32_;
goto v___jp_12_;
}
else
{
lean_object* v_val_33_; 
v_val_33_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_val_33_);
lean_dec_ref_known(v___x_30_, 1);
v___y_13_ = v___y_29_;
v___y_14_ = v_val_33_;
goto v___jp_12_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___boxed(lean_object* v_inst_38_, lean_object* v_s_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_38_, v_s_39_);
lean_dec(v_s_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(lean_object* v_m_41_, lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_s_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_42_, v_s_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___boxed(lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_s_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange(v_m_46_, v_inst_47_, v_inst_48_, v_s_49_);
lean_dec(v_s_49_);
lean_dec(v_inst_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(lean_object* v_env_52_, lean_object* v_contents_53_, lean_object* v_p_54_, lean_object* v_ictx_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_toPure_58_, lean_object* v_____do__lift_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v_s_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_60_ = lean_box(0);
v___x_61_ = lean_box(0);
lean_inc_ref(v_env_52_);
v___x_62_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_62_, 0, v_env_52_);
lean_ctor_set(v___x_62_, 1, v_____do__lift_59_);
lean_ctor_set(v___x_62_, 2, v___x_60_);
lean_ctor_set(v___x_62_, 3, v___x_61_);
v___x_63_ = l_Lean_Parser_getTokenTable(v_env_52_);
v___x_64_ = l_Lean_Parser_mkParserState(v_contents_53_);
lean_inc_ref(v_ictx_55_);
v_s_65_ = l_Lean_Parser_ParserFn_run(v_p_54_, v_ictx_55_, v___x_62_, v___x_63_, v___x_64_);
lean_inc_ref(v_s_65_);
v___x_66_ = l_Lean_Parser_ParserState_allErrors(v_s_65_);
v___x_67_ = lean_array_get_size(v___x_66_);
lean_dec_ref(v___x_66_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_nat_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_toPure_58_);
v___x_70_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_55_, v_s_65_);
v___x_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofFormat(v___x_71_);
v___x_73_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_stxStack_74_; lean_object* v_pos_75_; uint8_t v___x_76_; 
v_stxStack_74_ = lean_ctor_get(v_s_65_, 0);
lean_inc_ref(v_stxStack_74_);
v_pos_75_ = lean_ctor_get(v_s_65_, 2);
lean_inc(v_pos_75_);
v___x_76_ = l_Lean_Parser_InputContext_atEnd(v_ictx_55_, v_pos_75_);
lean_dec(v_pos_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v_stxStack_74_);
lean_dec(v_toPure_58_);
v___x_77_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_78_ = l_Lean_Parser_ParserState_mkError(v_s_65_, v___x_77_);
v___x_79_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_55_, v___x_78_);
v___x_80_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
v___x_81_ = l_Lean_MessageData_ofFormat(v___x_80_);
v___x_82_ = l_Lean_throwError___redArg(v_inst_56_, v_inst_57_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v_s_65_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
lean_dec_ref(v_ictx_55_);
v___x_83_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_74_);
lean_dec_ref(v_stxStack_74_);
v___x_84_ = lean_apply_2(v_toPure_58_, lean_box(0), v___x_83_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed(lean_object* v_env_85_, lean_object* v_contents_86_, lean_object* v_p_87_, lean_object* v_ictx_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_toPure_91_, lean_object* v_____do__lift_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0(v_env_85_, v_contents_86_, v_p_87_, v_ictx_88_, v_inst_89_, v_inst_90_, v_toPure_91_, v_____do__lift_92_);
lean_dec_ref(v_contents_86_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1(lean_object* v_contents_94_, lean_object* v_env_95_, lean_object* v_p_96_, lean_object* v_inst_97_, lean_object* v_inst_98_, lean_object* v_toPure_99_, lean_object* v_toBind_100_, lean_object* v_inst_101_, lean_object* v_____do__lift_102_){
_start:
{
uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v_ictx_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v___x_103_ = 1;
v___x_104_ = lean_string_utf8_byte_size(v_contents_94_);
lean_inc_ref(v_contents_94_);
v_ictx_105_ = l_Lean_Parser_mkInputContext___redArg(v_contents_94_, v_____do__lift_102_, v___x_103_, v___x_104_);
v___f_106_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_106_, 0, v_env_95_);
lean_closure_set(v___f_106_, 1, v_contents_94_);
lean_closure_set(v___f_106_, 2, v_p_96_);
lean_closure_set(v___f_106_, 3, v_ictx_105_);
lean_closure_set(v___f_106_, 4, v_inst_97_);
lean_closure_set(v___f_106_, 5, v_inst_98_);
lean_closure_set(v___f_106_, 6, v_toPure_99_);
v___x_107_ = lean_apply_4(v_toBind_100_, lean_box(0), lean_box(0), v_inst_101_, v___f_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2(lean_object* v_inst_108_, lean_object* v_contents_109_, lean_object* v_p_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_toPure_113_, lean_object* v_toBind_114_, lean_object* v_inst_115_, lean_object* v_env_116_){
_start:
{
lean_object* v_getFileName_117_; lean_object* v___f_118_; lean_object* v___x_119_; 
v_getFileName_117_ = lean_ctor_get(v_inst_108_, 2);
lean_inc(v_getFileName_117_);
lean_dec_ref(v_inst_108_);
lean_inc(v_toBind_114_);
v___f_118_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__1), 9, 8);
lean_closure_set(v___f_118_, 0, v_contents_109_);
lean_closure_set(v___f_118_, 1, v_env_116_);
lean_closure_set(v___f_118_, 2, v_p_110_);
lean_closure_set(v___f_118_, 3, v_inst_111_);
lean_closure_set(v___f_118_, 4, v_inst_112_);
lean_closure_set(v___f_118_, 5, v_toPure_113_);
lean_closure_set(v___f_118_, 6, v_toBind_114_);
lean_closure_set(v___f_118_, 7, v_inst_115_);
v___x_119_ = lean_apply_4(v_toBind_114_, lean_box(0), lean_box(0), v_getFileName_117_, v___f_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_p_125_, lean_object* v_contents_126_){
_start:
{
lean_object* v_toApplicative_127_; lean_object* v_toBind_128_; lean_object* v_getEnv_129_; lean_object* v_toPure_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
v_toApplicative_127_ = lean_ctor_get(v_inst_120_, 0);
v_toBind_128_ = lean_ctor_get(v_inst_120_, 1);
lean_inc_n(v_toBind_128_, 2);
v_getEnv_129_ = lean_ctor_get(v_inst_121_, 0);
lean_inc(v_getEnv_129_);
lean_dec_ref(v_inst_121_);
v_toPure_130_ = lean_ctor_get(v_toApplicative_127_, 1);
lean_inc(v_toPure_130_);
v___f_131_ = lean_alloc_closure((void*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__2), 9, 8);
lean_closure_set(v___f_131_, 0, v_inst_123_);
lean_closure_set(v___f_131_, 1, v_contents_126_);
lean_closure_set(v___f_131_, 2, v_p_125_);
lean_closure_set(v___f_131_, 3, v_inst_120_);
lean_closure_set(v___f_131_, 4, v_inst_122_);
lean_closure_set(v___f_131_, 5, v_toPure_130_);
lean_closure_set(v___f_131_, 6, v_toBind_128_);
lean_closure_set(v___f_131_, 7, v_inst_124_);
v___x_132_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v_getEnv_129_, v___f_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents(lean_object* v_m_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_p_139_, lean_object* v_contents_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_134_, v_inst_135_, v_inst_136_, v_inst_137_, v_inst_138_, v_p_139_, v_contents_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__0(lean_object* v_env_142_, lean_object* v_p_143_, lean_object* v_ictx_144_, lean_object* v_s_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_toPure_148_, lean_object* v_____do__lift_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_s_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_150_ = lean_box(0);
v___x_151_ = lean_box(0);
lean_inc_ref(v_env_142_);
v___x_152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_152_, 0, v_env_142_);
lean_ctor_set(v___x_152_, 1, v_____do__lift_149_);
lean_ctor_set(v___x_152_, 2, v___x_150_);
lean_ctor_set(v___x_152_, 3, v___x_151_);
v___x_153_ = l_Lean_Parser_getTokenTable(v_env_142_);
lean_inc_ref(v_ictx_144_);
v_s_154_ = l_Lean_Parser_ParserFn_run(v_p_143_, v_ictx_144_, v___x_152_, v___x_153_, v_s_145_);
lean_inc_ref(v_s_154_);
v___x_155_ = l_Lean_Parser_ParserState_allErrors(v_s_154_);
v___x_156_ = lean_array_get_size(v___x_155_);
lean_dec_ref(v___x_155_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = lean_nat_dec_eq(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_toPure_148_);
v___x_159_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_144_, v_s_154_);
v___x_160_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
v___x_161_ = l_Lean_MessageData_ofFormat(v___x_160_);
v___x_162_ = l_Lean_throwError___redArg(v_inst_146_, v_inst_147_, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v_stxStack_163_; lean_object* v_pos_164_; uint8_t v___x_165_; 
v_stxStack_163_ = lean_ctor_get(v_s_154_, 0);
lean_inc_ref(v_stxStack_163_);
v_pos_164_ = lean_ctor_get(v_s_154_, 2);
lean_inc(v_pos_164_);
v___x_165_ = l_Lean_Parser_InputContext_atEnd(v_ictx_144_, v_pos_164_);
lean_dec(v_pos_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
lean_dec_ref(v_stxStack_163_);
lean_dec(v_toPure_148_);
v___x_166_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_167_ = l_Lean_Parser_ParserState_mkError(v_s_154_, v___x_166_);
v___x_168_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_144_, v___x_167_);
v___x_169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v___x_170_ = l_Lean_MessageData_ofFormat(v___x_169_);
v___x_171_ = l_Lean_throwError___redArg(v_inst_146_, v_inst_147_, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec_ref(v_s_154_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
lean_dec_ref(v_ictx_144_);
v___x_172_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_163_);
lean_dec_ref(v_stxStack_163_);
v___x_173_ = lean_apply_2(v_toPure_148_, lean_box(0), v___x_172_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1(lean_object* v_source_174_, uint8_t v___x_175_, lean_object* v___y_176_, lean_object* v_start_177_, lean_object* v_env_178_, lean_object* v_p_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_toPure_182_, lean_object* v_toBind_183_, lean_object* v_inst_184_, lean_object* v_____do__lift_185_){
_start:
{
lean_object* v_ictx_186_; lean_object* v___x_187_; lean_object* v_s_188_; lean_object* v___f_189_; lean_object* v___x_190_; 
lean_inc_ref(v_source_174_);
v_ictx_186_ = l_Lean_Parser_mkInputContext___redArg(v_source_174_, v_____do__lift_185_, v___x_175_, v___y_176_);
v___x_187_ = l_Lean_Parser_mkParserState(v_source_174_);
lean_dec_ref(v_source_174_);
v_s_188_ = l_Lean_Parser_ParserState_setPos(v___x_187_, v_start_177_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__0), 8, 7);
lean_closure_set(v___f_189_, 0, v_env_178_);
lean_closure_set(v___f_189_, 1, v_p_179_);
lean_closure_set(v___f_189_, 2, v_ictx_186_);
lean_closure_set(v___f_189_, 3, v_s_188_);
lean_closure_set(v___f_189_, 4, v_inst_180_);
lean_closure_set(v___f_189_, 5, v_inst_181_);
lean_closure_set(v___f_189_, 6, v_toPure_182_);
v___x_190_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v_inst_184_, v___f_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__1___boxed(lean_object* v_source_191_, lean_object* v___x_192_, lean_object* v___y_193_, lean_object* v_start_194_, lean_object* v_env_195_, lean_object* v_p_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_toPure_199_, lean_object* v_toBind_200_, lean_object* v_inst_201_, lean_object* v_____do__lift_202_){
_start:
{
uint8_t v___x_357__boxed_203_; lean_object* v_res_204_; 
v___x_357__boxed_203_ = lean_unbox(v___x_192_);
v_res_204_ = l_Lean_Doc_parseContent___redArg___lam__1(v_source_191_, v___x_357__boxed_203_, v___y_193_, v_start_194_, v_env_195_, v_p_196_, v_inst_197_, v_inst_198_, v_toPure_199_, v_toBind_200_, v_inst_201_, v_____do__lift_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2(lean_object* v_text_205_, lean_object* v_inst_206_, uint8_t v___x_207_, lean_object* v_env_208_, lean_object* v_p_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_toPure_212_, lean_object* v_toBind_213_, lean_object* v_inst_214_, lean_object* v_____x_215_){
_start:
{
lean_object* v_start_216_; lean_object* v_stop_217_; lean_object* v_source_218_; lean_object* v___y_220_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_start_216_ = lean_ctor_get(v_____x_215_, 0);
lean_inc(v_start_216_);
v_stop_217_ = lean_ctor_get(v_____x_215_, 1);
lean_inc(v_stop_217_);
lean_dec_ref(v_____x_215_);
v_source_218_ = lean_ctor_get(v_text_205_, 0);
lean_inc_ref(v_source_218_);
lean_dec_ref(v_text_205_);
v___x_225_ = lean_string_utf8_byte_size(v_source_218_);
v___x_226_ = lean_nat_dec_le(v_stop_217_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec(v_stop_217_);
v___y_220_ = v___x_225_;
goto v___jp_219_;
}
else
{
v___y_220_ = v_stop_217_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v_getFileName_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___x_224_; 
v_getFileName_221_ = lean_ctor_get(v_inst_206_, 2);
lean_inc(v_getFileName_221_);
lean_dec_ref(v_inst_206_);
v___x_222_ = lean_box(v___x_207_);
lean_inc(v_toBind_213_);
v___f_223_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_223_, 0, v_source_218_);
lean_closure_set(v___f_223_, 1, v___x_222_);
lean_closure_set(v___f_223_, 2, v___y_220_);
lean_closure_set(v___f_223_, 3, v_start_216_);
lean_closure_set(v___f_223_, 4, v_env_208_);
lean_closure_set(v___f_223_, 5, v_p_209_);
lean_closure_set(v___f_223_, 6, v_inst_210_);
lean_closure_set(v___f_223_, 7, v_inst_211_);
lean_closure_set(v___f_223_, 8, v_toPure_212_);
lean_closure_set(v___f_223_, 9, v_toBind_213_);
lean_closure_set(v___f_223_, 10, v_inst_214_);
v___x_224_ = lean_apply_4(v_toBind_213_, lean_box(0), lean_box(0), v_getFileName_221_, v___f_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__2___boxed(lean_object* v_text_227_, lean_object* v_inst_228_, lean_object* v___x_229_, lean_object* v_env_230_, lean_object* v_p_231_, lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_toPure_234_, lean_object* v_toBind_235_, lean_object* v_inst_236_, lean_object* v_____x_237_){
_start:
{
uint8_t v___x_385__boxed_238_; lean_object* v_res_239_; 
v___x_385__boxed_238_ = lean_unbox(v___x_229_);
v_res_239_ = l_Lean_Doc_parseContent___redArg___lam__2(v_text_227_, v_inst_228_, v___x_385__boxed_238_, v_env_230_, v_p_231_, v_inst_232_, v_inst_233_, v_toPure_234_, v_toBind_235_, v_inst_236_, v_____x_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3(lean_object* v_text_240_, lean_object* v_inst_241_, uint8_t v___x_242_, lean_object* v_p_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_toPure_246_, lean_object* v_toBind_247_, lean_object* v_inst_248_, lean_object* v_tok_249_, lean_object* v_env_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_box(v___x_242_);
lean_inc(v_toBind_247_);
lean_inc_ref(v_inst_244_);
v___f_252_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_252_, 0, v_text_240_);
lean_closure_set(v___f_252_, 1, v_inst_241_);
lean_closure_set(v___f_252_, 2, v___x_251_);
lean_closure_set(v___f_252_, 3, v_env_250_);
lean_closure_set(v___f_252_, 4, v_p_243_);
lean_closure_set(v___f_252_, 5, v_inst_244_);
lean_closure_set(v___f_252_, 6, v_inst_245_);
lean_closure_set(v___f_252_, 7, v_toPure_246_);
lean_closure_set(v___f_252_, 8, v_toBind_247_);
lean_closure_set(v___f_252_, 9, v_inst_248_);
v___x_253_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_244_, v_tok_249_);
v___x_254_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_253_, v___f_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__3___boxed(lean_object* v_text_255_, lean_object* v_inst_256_, lean_object* v___x_257_, lean_object* v_p_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_toPure_261_, lean_object* v_toBind_262_, lean_object* v_inst_263_, lean_object* v_tok_264_, lean_object* v_env_265_){
_start:
{
uint8_t v___x_421__boxed_266_; lean_object* v_res_267_; 
v___x_421__boxed_266_ = lean_unbox(v___x_257_);
v_res_267_ = l_Lean_Doc_parseContent___redArg___lam__3(v_text_255_, v_inst_256_, v___x_421__boxed_266_, v_p_258_, v_inst_259_, v_inst_260_, v_toPure_261_, v_toBind_262_, v_inst_263_, v_tok_264_, v_env_265_);
lean_dec(v_tok_264_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4(lean_object* v_inst_268_, lean_object* v_inst_269_, uint8_t v___x_270_, lean_object* v_p_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_toPure_274_, lean_object* v_toBind_275_, lean_object* v_inst_276_, lean_object* v_tok_277_, lean_object* v_text_278_){
_start:
{
lean_object* v_getEnv_279_; lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___x_282_; 
v_getEnv_279_ = lean_ctor_get(v_inst_268_, 0);
lean_inc(v_getEnv_279_);
lean_dec_ref(v_inst_268_);
v___x_280_ = lean_box(v___x_270_);
lean_inc(v_toBind_275_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__3___boxed), 11, 10);
lean_closure_set(v___f_281_, 0, v_text_278_);
lean_closure_set(v___f_281_, 1, v_inst_269_);
lean_closure_set(v___f_281_, 2, v___x_280_);
lean_closure_set(v___f_281_, 3, v_p_271_);
lean_closure_set(v___f_281_, 4, v_inst_272_);
lean_closure_set(v___f_281_, 5, v_inst_273_);
lean_closure_set(v___f_281_, 6, v_toPure_274_);
lean_closure_set(v___f_281_, 7, v_toBind_275_);
lean_closure_set(v___f_281_, 8, v_inst_276_);
lean_closure_set(v___f_281_, 9, v_tok_277_);
v___x_282_ = lean_apply_4(v_toBind_275_, lean_box(0), lean_box(0), v_getEnv_279_, v___f_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg___lam__4___boxed(lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v___x_285_, lean_object* v_p_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_toPure_289_, lean_object* v_toBind_290_, lean_object* v_inst_291_, lean_object* v_tok_292_, lean_object* v_text_293_){
_start:
{
uint8_t v___x_445__boxed_294_; lean_object* v_res_295_; 
v___x_445__boxed_294_ = lean_unbox(v___x_285_);
v_res_295_ = l_Lean_Doc_parseContent___redArg___lam__4(v_inst_283_, v_inst_284_, v___x_445__boxed_294_, v_p_286_, v_inst_287_, v_inst_288_, v_toPure_289_, v_toBind_290_, v_inst_291_, v_tok_292_, v_text_293_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent___redArg(lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_p_302_, lean_object* v_tok_303_, lean_object* v_contents_304_){
_start:
{
uint8_t v___x_305_; uint8_t v___y_307_; lean_object* v___x_315_; 
v___x_305_ = 1;
v___x_315_ = l_Lean_Syntax_getPos_x3f(v_tok_303_, v___x_305_);
if (lean_obj_tag(v___x_315_) == 0)
{
v___y_307_ = v___x_305_;
goto v___jp_306_;
}
else
{
uint8_t v___x_316_; 
lean_dec_ref_known(v___x_315_, 1);
v___x_316_ = 0;
v___y_307_ = v___x_316_;
goto v___jp_306_;
}
v___jp_306_:
{
if (v___y_307_ == 0)
{
lean_object* v_toApplicative_308_; lean_object* v_toBind_309_; lean_object* v_toPure_310_; lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___x_313_; 
v_toApplicative_308_ = lean_ctor_get(v_inst_296_, 0);
lean_dec_ref(v_contents_304_);
v_toBind_309_ = lean_ctor_get(v_inst_296_, 1);
lean_inc_n(v_toBind_309_, 2);
v_toPure_310_ = lean_ctor_get(v_toApplicative_308_, 1);
lean_inc(v_toPure_310_);
v___x_311_ = lean_box(v___x_305_);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent___redArg___lam__4___boxed), 11, 10);
lean_closure_set(v___f_312_, 0, v_inst_298_);
lean_closure_set(v___f_312_, 1, v_inst_300_);
lean_closure_set(v___f_312_, 2, v___x_311_);
lean_closure_set(v___f_312_, 3, v_p_302_);
lean_closure_set(v___f_312_, 4, v_inst_296_);
lean_closure_set(v___f_312_, 5, v_inst_299_);
lean_closure_set(v___f_312_, 6, v_toPure_310_);
lean_closure_set(v___f_312_, 7, v_toBind_309_);
lean_closure_set(v___f_312_, 8, v_inst_301_);
lean_closure_set(v___f_312_, 9, v_tok_303_);
v___x_313_ = lean_apply_4(v_toBind_309_, lean_box(0), lean_box(0), v_inst_297_, v___f_312_);
return v___x_313_;
}
else
{
lean_object* v___x_314_; 
lean_dec(v_tok_303_);
lean_dec(v_inst_297_);
v___x_314_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_296_, v_inst_298_, v_inst_299_, v_inst_300_, v_inst_301_, v_p_302_, v_contents_304_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent(lean_object* v_m_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_p_324_, lean_object* v_tok_325_, lean_object* v_contents_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Doc_parseContent___redArg(v_inst_318_, v_inst_319_, v_inst_320_, v_inst_321_, v_inst_322_, v_inst_323_, v_p_324_, v_tok_325_, v_contents_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(lean_object* v_str_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_346_; 
v_fst_330_ = lean_ctor_get(v_a_329_, 0);
v_snd_331_ = lean_ctor_get(v_a_329_, 1);
v_isSharedCheck_346_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_346_ == 0)
{
v___x_333_ = v_a_329_;
v_isShared_334_ = v_isSharedCheck_346_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_inc(v_fst_330_);
lean_dec(v_a_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_346_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_dec_le(v___x_335_, v_fst_330_);
if (v___x_336_ == 0)
{
lean_object* v___x_338_; 
if (v_isShared_334_ == 0)
{
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_snd_331_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_340_ = lean_string_utf8_prev(v_str_328_, v_fst_330_);
lean_dec(v_fst_330_);
v___x_341_ = lean_nat_add(v_snd_331_, v___x_335_);
lean_dec(v_snd_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_341_);
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_343_ = v___x_333_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_341_);
v___x_343_ = v_reuseFailAlloc_345_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
v_a_329_ = v___x_343_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg___boxed(lean_object* v_str_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_347_, v_a_348_);
lean_dec_ref(v_str_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(lean_object* v_str_350_, lean_object* v_p_351_){
_start:
{
lean_object* v_n_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_snd_355_; 
v_n_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_353_, 0, v_p_351_);
lean_ctor_set(v___x_353_, 1, v_n_352_);
v___x_354_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_350_, v___x_353_);
v_snd_355_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_snd_355_);
lean_dec_ref(v___x_354_);
return v_snd_355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex___boxed(lean_object* v_str_356_, lean_object* v_p_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_356_, v_p_357_);
lean_dec_ref(v_str_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(lean_object* v_str_359_, lean_object* v_inst_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___redArg(v_str_359_, v_a_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0___boxed(lean_object* v_str_363_, lean_object* v_inst_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex_spec__0(v_str_363_, v_inst_364_, v_a_365_);
lean_dec_ref(v_str_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(lean_object* v_str_367_, lean_object* v_p_368_, lean_object* v_j_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_zero_371_; uint8_t v_isZero_372_; 
v_zero_371_ = lean_unsigned_to_nat(0u);
v_isZero_372_ = lean_nat_dec_eq(v_j_369_, v_zero_371_);
if (v_isZero_372_ == 1)
{
lean_dec(v_j_369_);
return v_a_370_;
}
else
{
lean_object* v_one_373_; lean_object* v_n_374_; lean_object* v___x_375_; 
lean_dec(v_a_370_);
v_one_373_ = lean_unsigned_to_nat(1u);
v_n_374_ = lean_nat_sub(v_j_369_, v_one_373_);
lean_dec(v_j_369_);
v___x_375_ = lean_string_utf8_next(v_str_367_, v_p_368_);
v_j_369_ = v_n_374_;
v_a_370_ = v___x_375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg___boxed(lean_object* v_str_377_, lean_object* v_p_378_, lean_object* v_j_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_377_, v_p_378_, v_j_379_, v_a_380_);
lean_dec(v_p_378_);
lean_dec_ref(v_str_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(lean_object* v_str_382_, lean_object* v_n_383_, lean_object* v_p_384_){
_start:
{
lean_object* v___x_385_; 
lean_inc(v_p_384_);
v___x_385_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_382_, v_p_384_, v_n_383_, v_p_384_);
lean_dec(v_p_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn___boxed(lean_object* v_str_386_, lean_object* v_n_387_, lean_object* v_p_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn(v_str_386_, v_n_387_, v_p_388_);
lean_dec_ref(v_str_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(lean_object* v_str_390_, lean_object* v_p_391_, lean_object* v_n_392_, lean_object* v_j_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_str_390_, v_p_391_, v_j_393_, v_a_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___boxed(lean_object* v_str_397_, lean_object* v_p_398_, lean_object* v_n_399_, lean_object* v_j_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0(v_str_397_, v_p_398_, v_n_399_, v_j_400_, v_a_401_, v_a_402_);
lean_dec(v_n_399_);
lean_dec(v_p_398_);
lean_dec_ref(v_str_397_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(lean_object* v_text_404_, lean_object* v_posOfStr_405_, lean_object* v_str_406_, lean_object* v_posInStr_407_){
_start:
{
lean_object* v_source_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_source_408_ = lean_ctor_get(v_text_404_, 0);
v___x_409_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_posIndex(v_str_406_, v_posInStr_407_);
lean_inc(v_posOfStr_405_);
v___x_410_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_nextn_spec__0___redArg(v_source_408_, v_posOfStr_405_, v___x_409_, v_posOfStr_405_);
lean_dec(v_posOfStr_405_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition___boxed(lean_object* v_text_411_, lean_object* v_posOfStr_412_, lean_object* v_str_413_, lean_object* v_posInStr_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_411_, v_posOfStr_412_, v_str_413_, v_posInStr_414_);
lean_dec_ref(v_str_413_);
lean_dec_ref(v_text_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(lean_object* v_text_416_, lean_object* v_posOfStr_417_, lean_object* v_str_418_, lean_object* v_a_419_){
_start:
{
switch(lean_obj_tag(v_a_419_))
{
case 0:
{
lean_object* v_pos_420_; lean_object* v_endPos_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
v_pos_420_ = lean_ctor_get(v_a_419_, 1);
lean_inc(v_pos_420_);
v_endPos_421_ = lean_ctor_get(v_a_419_, 3);
lean_inc(v_endPos_421_);
lean_dec_ref_known(v_a_419_, 4);
lean_inc(v_posOfStr_417_);
v___x_422_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_416_, v_posOfStr_417_, v_str_418_, v_pos_420_);
v___x_423_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_416_, v_posOfStr_417_, v_str_418_, v_endPos_421_);
v___x_424_ = 1;
v___x_425_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_425_, 0, v___x_422_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set_uint8(v___x_425_, sizeof(void*)*2, v___x_424_);
return v___x_425_;
}
case 1:
{
lean_object* v_pos_426_; lean_object* v_endPos_427_; uint8_t v_canonical_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_437_; 
v_pos_426_ = lean_ctor_get(v_a_419_, 0);
v_endPos_427_ = lean_ctor_get(v_a_419_, 1);
v_canonical_428_ = lean_ctor_get_uint8(v_a_419_, sizeof(void*)*2);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_419_);
if (v_isSharedCheck_437_ == 0)
{
v___x_430_ = v_a_419_;
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_endPos_427_);
lean_inc(v_pos_426_);
lean_dec(v_a_419_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_437_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_posOfStr_417_);
v___x_432_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_416_, v_posOfStr_417_, v_str_418_, v_pos_426_);
v___x_433_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_416_, v_posOfStr_417_, v_str_418_, v_endPos_427_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_433_);
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_435_ = v___x_430_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___x_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*2, v_canonical_428_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
default: 
{
lean_dec(v_posOfStr_417_);
return v_a_419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo___boxed(lean_object* v_text_438_, lean_object* v_posOfStr_439_, lean_object* v_str_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_438_, v_posOfStr_439_, v_str_440_, v_a_441_);
lean_dec_ref(v_str_440_);
lean_dec_ref(v_text_438_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(lean_object* v_text_443_, lean_object* v_posOfStr_444_, lean_object* v_str_445_, lean_object* v_a_446_){
_start:
{
switch(lean_obj_tag(v_a_446_))
{
case 0:
{
lean_dec(v_posOfStr_444_);
return v_a_446_;
}
case 1:
{
lean_object* v_info_447_; lean_object* v_kind_448_; lean_object* v_args_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_460_; 
v_info_447_ = lean_ctor_get(v_a_446_, 0);
v_kind_448_ = lean_ctor_get(v_a_446_, 1);
v_args_449_ = lean_ctor_get(v_a_446_, 2);
v_isSharedCheck_460_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_460_ == 0)
{
v___x_451_ = v_a_446_;
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_args_449_);
lean_inc(v_kind_448_);
lean_inc(v_info_447_);
lean_dec(v_a_446_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_460_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; size_t v_sz_454_; size_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
lean_inc(v_posOfStr_444_);
v___x_453_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_443_, v_posOfStr_444_, v_str_445_, v_info_447_);
v_sz_454_ = lean_array_size(v_args_449_);
v___x_455_ = ((size_t)0ULL);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_443_, v_posOfStr_444_, v_str_445_, v_sz_454_, v___x_455_, v_args_449_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 2, v___x_456_);
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_458_ = v___x_451_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_kind_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
case 2:
{
lean_object* v_info_461_; lean_object* v_val_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_470_; 
v_info_461_ = lean_ctor_get(v_a_446_, 0);
v_val_462_ = lean_ctor_get(v_a_446_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_470_ == 0)
{
v___x_464_ = v_a_446_;
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_val_462_);
lean_inc(v_info_461_);
lean_dec(v_a_446_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_470_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_466_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_443_, v_posOfStr_444_, v_str_445_, v_info_461_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_466_);
v___x_468_ = v___x_464_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_val_462_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
default: 
{
lean_object* v_info_471_; lean_object* v_rawVal_472_; lean_object* v_val_473_; lean_object* v_preresolved_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
v_info_471_ = lean_ctor_get(v_a_446_, 0);
v_rawVal_472_ = lean_ctor_get(v_a_446_, 1);
v_val_473_ = lean_ctor_get(v_a_446_, 2);
v_preresolved_474_ = lean_ctor_get(v_a_446_, 3);
v_isSharedCheck_482_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_482_ == 0)
{
v___x_476_ = v_a_446_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_preresolved_474_);
lean_inc(v_val_473_);
lean_inc(v_rawVal_472_);
lean_inc(v_info_471_);
lean_dec(v_a_446_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionInfo(v_text_443_, v_posOfStr_444_, v_str_445_, v_info_471_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_rawVal_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_val_473_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_preresolved_474_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(lean_object* v_text_483_, lean_object* v_posOfStr_484_, lean_object* v_str_485_, size_t v_sz_486_, size_t v_i_487_, lean_object* v_bs_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_489_ == 0)
{
lean_dec(v_posOfStr_484_);
return v_bs_488_;
}
else
{
lean_object* v_v_490_; lean_object* v___x_491_; lean_object* v_bs_x27_492_; lean_object* v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v_v_490_ = lean_array_uget(v_bs_488_, v_i_487_);
v___x_491_ = lean_unsigned_to_nat(0u);
v_bs_x27_492_ = lean_array_uset(v_bs_488_, v_i_487_, v___x_491_);
lean_inc(v_posOfStr_484_);
v___x_493_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_483_, v_posOfStr_484_, v_str_485_, v_v_490_);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_487_, v___x_494_);
v___x_496_ = lean_array_uset(v_bs_x27_492_, v_i_487_, v___x_493_);
v_i_487_ = v___x_495_;
v_bs_488_ = v___x_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0___boxed(lean_object* v_text_498_, lean_object* v_posOfStr_499_, lean_object* v_str_500_, lean_object* v_sz_501_, lean_object* v_i_502_, lean_object* v_bs_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_501_);
lean_dec(v_sz_501_);
v_i_boxed_505_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_spec__0(v_text_498_, v_posOfStr_499_, v_str_500_, v_sz_boxed_504_, v_i_boxed_505_, v_bs_503_);
lean_dec_ref(v_str_500_);
lean_dec_ref(v_text_498_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax___boxed(lean_object* v_text_507_, lean_object* v_posOfStr_508_, lean_object* v_str_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_507_, v_posOfStr_508_, v_str_509_, v_a_510_);
lean_dec_ref(v_str_509_);
lean_dec_ref(v_text_507_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter___redArg(lean_object* v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_, lean_object* v_h__3_515_, lean_object* v_h__4_516_){
_start:
{
switch(lean_obj_tag(v_x_512_))
{
case 0:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v___x_517_ = lean_box(0);
v___x_518_ = lean_apply_1(v_h__4_516_, v___x_517_);
return v___x_518_;
}
case 1:
{
lean_object* v_info_519_; lean_object* v_kind_520_; lean_object* v_args_521_; lean_object* v___x_522_; 
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__2_514_);
v_info_519_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_info_519_);
v_kind_520_ = lean_ctor_get(v_x_512_, 1);
lean_inc(v_kind_520_);
v_args_521_ = lean_ctor_get(v_x_512_, 2);
lean_inc_ref(v_args_521_);
lean_dec_ref_known(v_x_512_, 3);
v___x_522_ = lean_apply_3(v_h__1_513_, v_info_519_, v_kind_520_, v_args_521_);
return v___x_522_;
}
case 2:
{
lean_object* v_info_523_; lean_object* v_val_524_; lean_object* v___x_525_; 
lean_dec(v_h__4_516_);
lean_dec(v_h__2_514_);
lean_dec(v_h__1_513_);
v_info_523_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_info_523_);
v_val_524_ = lean_ctor_get(v_x_512_, 1);
lean_inc_ref(v_val_524_);
lean_dec_ref_known(v_x_512_, 2);
v___x_525_ = lean_apply_2(v_h__3_515_, v_info_523_, v_val_524_);
return v___x_525_;
}
default: 
{
lean_object* v_info_526_; lean_object* v_rawVal_527_; lean_object* v_val_528_; lean_object* v_preresolved_529_; lean_object* v___x_530_; 
lean_dec(v_h__4_516_);
lean_dec(v_h__3_515_);
lean_dec(v_h__1_513_);
v_info_526_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_info_526_);
v_rawVal_527_ = lean_ctor_get(v_x_512_, 1);
lean_inc_ref(v_rawVal_527_);
v_val_528_ = lean_ctor_get(v_x_512_, 2);
lean_inc(v_val_528_);
v_preresolved_529_ = lean_ctor_get(v_x_512_, 3);
lean_inc(v_preresolved_529_);
lean_dec_ref_known(v_x_512_, 4);
v___x_530_ = lean_apply_4(v_h__2_514_, v_info_526_, v_rawVal_527_, v_val_528_, v_preresolved_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax_match__1_splitter(lean_object* v_motive_531_, lean_object* v_x_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_, lean_object* v_h__3_535_, lean_object* v_h__4_536_){
_start:
{
switch(lean_obj_tag(v_x_532_))
{
case 0:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_h__3_535_);
lean_dec(v_h__2_534_);
lean_dec(v_h__1_533_);
v___x_537_ = lean_box(0);
v___x_538_ = lean_apply_1(v_h__4_536_, v___x_537_);
return v___x_538_;
}
case 1:
{
lean_object* v_info_539_; lean_object* v_kind_540_; lean_object* v_args_541_; lean_object* v___x_542_; 
lean_dec(v_h__4_536_);
lean_dec(v_h__3_535_);
lean_dec(v_h__2_534_);
v_info_539_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_info_539_);
v_kind_540_ = lean_ctor_get(v_x_532_, 1);
lean_inc(v_kind_540_);
v_args_541_ = lean_ctor_get(v_x_532_, 2);
lean_inc_ref(v_args_541_);
lean_dec_ref_known(v_x_532_, 3);
v___x_542_ = lean_apply_3(v_h__1_533_, v_info_539_, v_kind_540_, v_args_541_);
return v___x_542_;
}
case 2:
{
lean_object* v_info_543_; lean_object* v_val_544_; lean_object* v___x_545_; 
lean_dec(v_h__4_536_);
lean_dec(v_h__2_534_);
lean_dec(v_h__1_533_);
v_info_543_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_info_543_);
v_val_544_ = lean_ctor_get(v_x_532_, 1);
lean_inc_ref(v_val_544_);
lean_dec_ref_known(v_x_532_, 2);
v___x_545_ = lean_apply_2(v_h__3_535_, v_info_543_, v_val_544_);
return v___x_545_;
}
default: 
{
lean_object* v_info_546_; lean_object* v_rawVal_547_; lean_object* v_val_548_; lean_object* v_preresolved_549_; lean_object* v___x_550_; 
lean_dec(v_h__4_536_);
lean_dec(v_h__3_535_);
lean_dec(v_h__1_533_);
v_info_546_ = lean_ctor_get(v_x_532_, 0);
lean_inc(v_info_546_);
v_rawVal_547_ = lean_ctor_get(v_x_532_, 1);
lean_inc_ref(v_rawVal_547_);
v_val_548_ = lean_ctor_get(v_x_532_, 2);
lean_inc(v_val_548_);
v_preresolved_549_ = lean_ctor_get(v_x_532_, 3);
lean_inc(v_preresolved_549_);
lean_dec_ref_known(v_x_532_, 4);
v___x_550_ = lean_apply_4(v_h__2_534_, v_info_546_, v_rawVal_547_, v_val_548_, v_preresolved_549_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter___redArg(lean_object* v_x_551_, lean_object* v_h__1_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = lean_apply_2(v_h__1_552_, v_x_551_, lean_box(0));
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DocString_Builtin_Parsing_0__Array_map__unattach_match__1_splitter(lean_object* v_00_u03b1_554_, lean_object* v_P_555_, lean_object* v_motive_556_, lean_object* v_x_557_, lean_object* v_h__1_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = lean_apply_2(v_h__1_558_, v_x_557_, lean_box(0));
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__0(lean_object* v_toPure_560_, lean_object* v_____do__lift_561_){
_start:
{
if (lean_obj_tag(v_____do__lift_561_) == 0)
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
v_a_562_ = lean_ctor_get(v_____do__lift_561_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_____do__lift_561_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v_____do__lift_561_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v_____do__lift_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 1);
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_apply_2(v_toPure_560_, lean_box(0), v___x_567_);
return v___x_568_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_a_571_ = lean_ctor_get(v_____do__lift_561_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_____do__lift_561_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v_____do__lift_561_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v_____do__lift_561_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 0);
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; 
v___x_577_ = lean_apply_2(v_toPure_560_, lean_box(0), v___x_576_);
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(lean_object* v_text_580_, lean_object* v_pos_581_, lean_object* v_str_582_, lean_object* v_x_583_){
_start:
{
lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v_fst_584_ = lean_ctor_get(v_x_583_, 0);
v_snd_585_ = lean_ctor_get(v_x_583_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_x_583_);
if (v_isSharedCheck_593_ == 0)
{
v___x_587_ = v_x_583_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_inc(v_fst_584_);
lean_dec(v_x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_589_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_580_, v_pos_581_, v_str_582_, v_fst_584_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_snd_585_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed(lean_object* v_text_594_, lean_object* v_pos_595_, lean_object* v_str_596_, lean_object* v_x_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__1(v_text_594_, v_pos_595_, v_str_596_, v_x_597_);
lean_dec_ref(v_str_596_);
lean_dec_ref(v_text_594_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(lean_object* v_env_618_, lean_object* v_p_619_, lean_object* v_ictx_620_, lean_object* v_s_621_, lean_object* v_text_622_, lean_object* v_pos_623_, lean_object* v_str_624_, lean_object* v___f_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_toPure_628_, lean_object* v_____do__lift_629_){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_s_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_630_ = lean_box(0);
v___x_631_ = lean_box(0);
lean_inc_ref(v_env_618_);
v___x_632_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_632_, 0, v_env_618_);
lean_ctor_set(v___x_632_, 1, v_____do__lift_629_);
lean_ctor_set(v___x_632_, 2, v___x_630_);
lean_ctor_set(v___x_632_, 3, v___x_631_);
v___x_633_ = l_Lean_Parser_getTokenTable(v_env_618_);
lean_inc_ref(v_ictx_620_);
v_s_634_ = l_Lean_Parser_ParserFn_run(v_p_619_, v_ictx_620_, v___x_632_, v___x_633_, v_s_621_);
lean_inc_ref(v_s_634_);
v___x_635_ = l_Lean_Parser_ParserState_allErrors(v_s_634_);
v___x_636_ = lean_array_get_size(v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_nat_dec_eq(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v_stxStack_639_; lean_object* v_lhsPrec_640_; lean_object* v_pos_641_; lean_object* v_cache_642_; lean_object* v_errorMsg_643_; lean_object* v_recoveredErrors_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_toPure_628_);
v_stxStack_639_ = lean_ctor_get(v_s_634_, 0);
v_lhsPrec_640_ = lean_ctor_get(v_s_634_, 1);
v_pos_641_ = lean_ctor_get(v_s_634_, 2);
v_cache_642_ = lean_ctor_get(v_s_634_, 3);
v_errorMsg_643_ = lean_ctor_get(v_s_634_, 4);
v_recoveredErrors_644_ = lean_ctor_get(v_s_634_, 5);
v_isSharedCheck_681_ = !lean_is_exclusive(v_s_634_);
if (v_isSharedCheck_681_ == 0)
{
v___x_646_ = v_s_634_;
v_isShared_647_ = v_isSharedCheck_681_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_recoveredErrors_644_);
lean_inc(v_errorMsg_643_);
lean_inc(v_cache_642_);
lean_inc(v_pos_641_);
lean_inc(v_lhsPrec_640_);
lean_inc(v_stxStack_639_);
lean_dec(v_s_634_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_681_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___y_650_; 
lean_inc(v_pos_623_);
v___x_648_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_reposition(v_text_622_, v_pos_623_, v_str_624_, v_pos_641_);
if (lean_obj_tag(v_errorMsg_643_) == 0)
{
lean_dec(v_pos_623_);
v___y_650_ = v_errorMsg_643_;
goto v___jp_649_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_680_; 
v_val_662_ = lean_ctor_get(v_errorMsg_643_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_errorMsg_643_);
if (v_isSharedCheck_680_ == 0)
{
v___x_664_ = v_errorMsg_643_;
v_isShared_665_ = v_isSharedCheck_680_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_val_662_);
lean_dec(v_errorMsg_643_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_680_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_unexpectedTk_666_; lean_object* v_unexpected_667_; lean_object* v_expected_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_679_; 
v_unexpectedTk_666_ = lean_ctor_get(v_val_662_, 0);
v_unexpected_667_ = lean_ctor_get(v_val_662_, 1);
v_expected_668_ = lean_ctor_get(v_val_662_, 2);
v_isSharedCheck_679_ = !lean_is_exclusive(v_val_662_);
if (v_isSharedCheck_679_ == 0)
{
v___x_670_ = v_val_662_;
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_expected_668_);
lean_inc(v_unexpected_667_);
lean_inc(v_unexpectedTk_666_);
lean_dec(v_val_662_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_622_, v_pos_623_, v_str_624_, v_unexpectedTk_666_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_unexpected_667_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_expected_668_);
v___x_674_ = v_reuseFailAlloc_678_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_674_);
v___x_676_ = v___x_664_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v___y_650_ = v___x_676_;
goto v___jp_649_;
}
}
}
}
}
v___jp_649_:
{
lean_object* v___x_651_; size_t v_sz_652_; size_t v___x_653_; lean_object* v___x_654_; lean_object* v_s_656_; 
v___x_651_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___closed__9));
v_sz_652_ = lean_array_size(v_recoveredErrors_644_);
v___x_653_ = ((size_t)0ULL);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_651_, v___f_625_, v_sz_652_, v___x_653_, v_recoveredErrors_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 5, v___x_654_);
lean_ctor_set(v___x_646_, 4, v___y_650_);
lean_ctor_set(v___x_646_, 2, v___x_648_);
v_s_656_ = v___x_646_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_stxStack_639_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_lhsPrec_640_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_cache_642_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v___y_650_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v___x_654_);
v_s_656_ = v_reuseFailAlloc_661_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_620_, v_s_656_);
v___x_658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___x_659_ = l_Lean_MessageData_ofFormat(v___x_658_);
v___x_660_ = l_Lean_throwError___redArg(v_inst_626_, v_inst_627_, v___x_659_);
return v___x_660_;
}
}
}
}
else
{
lean_object* v_stxStack_682_; lean_object* v_pos_683_; uint8_t v___x_684_; 
lean_dec_ref(v___f_625_);
v_stxStack_682_ = lean_ctor_get(v_s_634_, 0);
lean_inc_ref(v_stxStack_682_);
v_pos_683_ = lean_ctor_get(v_s_634_, 2);
lean_inc(v_pos_683_);
v___x_684_ = l_Lean_Parser_InputContext_atEnd(v_ictx_620_, v_pos_683_);
lean_dec(v_pos_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec_ref(v_stxStack_682_);
lean_dec(v_toPure_628_);
lean_dec(v_pos_623_);
v___x_685_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_686_ = l_Lean_Parser_ParserState_mkError(v_s_634_, v___x_685_);
v___x_687_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_620_, v___x_686_);
v___x_688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
v___x_689_ = l_Lean_MessageData_ofFormat(v___x_688_);
v___x_690_ = l_Lean_throwError___redArg(v_inst_626_, v_inst_627_, v___x_689_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec_ref(v_s_634_);
lean_dec_ref(v_inst_627_);
lean_dec_ref(v_inst_626_);
lean_dec_ref(v_ictx_620_);
v___x_691_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_682_);
lean_dec_ref(v_stxStack_682_);
v___x_692_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseQuotedStrLit_repositionSyntax(v_text_622_, v_pos_623_, v_str_624_, v___x_691_);
v___x_693_ = lean_apply_2(v_toPure_628_, lean_box(0), v___x_692_);
return v___x_693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed(lean_object* v_env_694_, lean_object* v_p_695_, lean_object* v_ictx_696_, lean_object* v_s_697_, lean_object* v_text_698_, lean_object* v_pos_699_, lean_object* v_str_700_, lean_object* v___f_701_, lean_object* v_inst_702_, lean_object* v_inst_703_, lean_object* v_toPure_704_, lean_object* v_____do__lift_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__2(v_env_694_, v_p_695_, v_ictx_696_, v_s_697_, v_text_698_, v_pos_699_, v_str_700_, v___f_701_, v_inst_702_, v_inst_703_, v_toPure_704_, v_____do__lift_705_);
lean_dec_ref(v_str_700_);
lean_dec_ref(v_text_698_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(lean_object* v_str_707_, uint8_t v___x_708_, lean_object* v_env_709_, lean_object* v_p_710_, lean_object* v_text_711_, lean_object* v_pos_712_, lean_object* v___f_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_toPure_716_, lean_object* v_toBind_717_, lean_object* v_inst_718_, lean_object* v_____do__lift_719_){
_start:
{
lean_object* v___x_720_; lean_object* v_ictx_721_; lean_object* v_s_722_; lean_object* v___f_723_; lean_object* v___x_724_; 
v___x_720_ = lean_string_utf8_byte_size(v_str_707_);
lean_inc_ref(v_str_707_);
v_ictx_721_ = l_Lean_Parser_mkInputContext___redArg(v_str_707_, v_____do__lift_719_, v___x_708_, v___x_720_);
v_s_722_ = l_Lean_Parser_mkParserState(v_str_707_);
v___f_723_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_723_, 0, v_env_709_);
lean_closure_set(v___f_723_, 1, v_p_710_);
lean_closure_set(v___f_723_, 2, v_ictx_721_);
lean_closure_set(v___f_723_, 3, v_s_722_);
lean_closure_set(v___f_723_, 4, v_text_711_);
lean_closure_set(v___f_723_, 5, v_pos_712_);
lean_closure_set(v___f_723_, 6, v_str_707_);
lean_closure_set(v___f_723_, 7, v___f_713_);
lean_closure_set(v___f_723_, 8, v_inst_714_);
lean_closure_set(v___f_723_, 9, v_inst_715_);
lean_closure_set(v___f_723_, 10, v_toPure_716_);
v___x_724_ = lean_apply_4(v_toBind_717_, lean_box(0), lean_box(0), v_inst_718_, v___f_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed(lean_object* v_str_725_, lean_object* v___x_726_, lean_object* v_env_727_, lean_object* v_p_728_, lean_object* v_text_729_, lean_object* v_pos_730_, lean_object* v___f_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_toPure_734_, lean_object* v_toBind_735_, lean_object* v_inst_736_, lean_object* v_____do__lift_737_){
_start:
{
uint8_t v___x_1044__boxed_738_; lean_object* v_res_739_; 
v___x_1044__boxed_738_ = lean_unbox(v___x_726_);
v_res_739_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__3(v_str_725_, v___x_1044__boxed_738_, v_env_727_, v_p_728_, v_text_729_, v_pos_730_, v___f_731_, v_inst_732_, v_inst_733_, v_toPure_734_, v_toBind_735_, v_inst_736_, v_____do__lift_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(lean_object* v_inst_740_, lean_object* v_strLit_741_, lean_object* v_text_742_, uint8_t v___x_743_, lean_object* v_env_744_, lean_object* v_p_745_, lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_toPure_748_, lean_object* v_toBind_749_, lean_object* v_inst_750_, lean_object* v_pos_751_){
_start:
{
lean_object* v_getFileName_752_; lean_object* v_str_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___f_756_; lean_object* v___x_757_; 
v_getFileName_752_ = lean_ctor_get(v_inst_740_, 2);
lean_inc(v_getFileName_752_);
lean_dec_ref(v_inst_740_);
v_str_753_ = l_Lean_TSyntax_getString(v_strLit_741_);
lean_inc_ref(v_str_753_);
lean_inc(v_pos_751_);
lean_inc_ref(v_text_742_);
v___f_754_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_754_, 0, v_text_742_);
lean_closure_set(v___f_754_, 1, v_pos_751_);
lean_closure_set(v___f_754_, 2, v_str_753_);
v___x_755_ = lean_box(v___x_743_);
lean_inc(v_toBind_749_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__3___boxed), 13, 12);
lean_closure_set(v___f_756_, 0, v_str_753_);
lean_closure_set(v___f_756_, 1, v___x_755_);
lean_closure_set(v___f_756_, 2, v_env_744_);
lean_closure_set(v___f_756_, 3, v_p_745_);
lean_closure_set(v___f_756_, 4, v_text_742_);
lean_closure_set(v___f_756_, 5, v_pos_751_);
lean_closure_set(v___f_756_, 6, v___f_754_);
lean_closure_set(v___f_756_, 7, v_inst_746_);
lean_closure_set(v___f_756_, 8, v_inst_747_);
lean_closure_set(v___f_756_, 9, v_toPure_748_);
lean_closure_set(v___f_756_, 10, v_toBind_749_);
lean_closure_set(v___f_756_, 11, v_inst_750_);
v___x_757_ = lean_apply_4(v_toBind_749_, lean_box(0), lean_box(0), v_getFileName_752_, v___f_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed(lean_object* v_inst_758_, lean_object* v_strLit_759_, lean_object* v_text_760_, lean_object* v___x_761_, lean_object* v_env_762_, lean_object* v_p_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_toPure_766_, lean_object* v_toBind_767_, lean_object* v_inst_768_, lean_object* v_pos_769_){
_start:
{
uint8_t v___x_1069__boxed_770_; lean_object* v_res_771_; 
v___x_1069__boxed_770_ = lean_unbox(v___x_761_);
v_res_771_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__4(v_inst_758_, v_strLit_759_, v_text_760_, v___x_1069__boxed_770_, v_env_762_, v_p_763_, v_inst_764_, v_inst_765_, v_toPure_766_, v_toBind_767_, v_inst_768_, v_pos_769_);
lean_dec(v_strLit_759_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__5(lean_object* v___f_772_, lean_object* v_pos_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = lean_apply_1(v___f_772_, v_pos_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__0));
v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(lean_object* v_text_778_, lean_object* v_inst_779_, lean_object* v_inst_780_, lean_object* v_strLit_781_, lean_object* v_toBind_782_, lean_object* v___f_783_, lean_object* v_toPure_784_, lean_object* v___f_785_, lean_object* v_____r_786_, lean_object* v_pos_787_){
_start:
{
lean_object* v_source_788_; uint32_t v___x_789_; uint32_t v___x_790_; uint8_t v___x_791_; 
v_source_788_ = lean_ctor_get(v_text_778_, 0);
v___x_789_ = lean_string_utf8_get(v_source_788_, v_pos_787_);
v___x_790_ = 34;
v___x_791_ = lean_uint32_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v___f_785_);
lean_dec(v_toPure_784_);
v___x_792_ = lean_obj_once(&l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1, &l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1_once, _init_l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___closed__1);
v___x_793_ = l_Lean_throwErrorAt___redArg(v_inst_779_, v_inst_780_, v_strLit_781_, v___x_792_);
v___x_794_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_793_, v___f_783_);
return v___x_794_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v___f_783_);
lean_dec(v_strLit_781_);
lean_dec_ref(v_inst_780_);
lean_dec_ref(v_inst_779_);
v___x_795_ = lean_string_utf8_next(v_source_788_, v_pos_787_);
v___x_796_ = lean_apply_2(v_toPure_784_, lean_box(0), v___x_795_);
v___x_797_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_796_, v___f_785_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed(lean_object* v_text_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_strLit_801_, lean_object* v_toBind_802_, lean_object* v___f_803_, lean_object* v_toPure_804_, lean_object* v___f_805_, lean_object* v_____r_806_, lean_object* v_pos_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__7(v_text_798_, v_inst_799_, v_inst_800_, v_strLit_801_, v_toBind_802_, v___f_803_, v_toPure_804_, v___f_805_, v_____r_806_, v_pos_807_);
lean_dec(v_pos_807_);
lean_dec_ref(v_text_798_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__6(lean_object* v___f_809_, lean_object* v_____s_810_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_box(0);
v___x_812_ = lean_apply_2(v___f_809_, v___x_811_, v_____s_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(lean_object* v_source_813_, lean_object* v_toPure_814_, lean_object* v_toBind_815_, lean_object* v___f_816_, lean_object* v_b_817_){
_start:
{
uint32_t v___x_818_; uint32_t v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_string_utf8_get(v_source_813_, v_b_817_);
v___x_819_ = 35;
v___x_820_ = lean_uint32_dec_eq(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_b_817_);
v___x_822_ = lean_apply_2(v_toPure_814_, lean_box(0), v___x_821_);
v___x_823_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v___x_822_, v___f_816_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_824_ = lean_string_utf8_next(v_source_813_, v_b_817_);
lean_dec(v_b_817_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
v___x_826_ = lean_apply_2(v_toPure_814_, lean_box(0), v___x_825_);
v___x_827_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v___x_826_, v___f_816_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed(lean_object* v_source_828_, lean_object* v_toPure_829_, lean_object* v_toBind_830_, lean_object* v___f_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__8(v_source_828_, v_toPure_829_, v_toBind_830_, v___f_831_, v_b_832_);
lean_dec_ref(v_source_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__9(lean_object* v_text_834_, lean_object* v___f_835_, lean_object* v_toPure_836_, lean_object* v_toBind_837_, lean_object* v___f_838_, lean_object* v_inst_839_, lean_object* v___f_840_, lean_object* v_____x_841_){
_start:
{
lean_object* v_start_842_; lean_object* v_source_843_; uint32_t v___x_844_; uint32_t v___x_845_; uint8_t v___x_846_; 
v_start_842_ = lean_ctor_get(v_____x_841_, 0);
lean_inc(v_start_842_);
lean_dec_ref(v_____x_841_);
v_source_843_ = lean_ctor_get(v_text_834_, 0);
lean_inc_ref(v_source_843_);
lean_dec_ref(v_text_834_);
v___x_844_ = lean_string_utf8_get(v_source_843_, v_start_842_);
v___x_845_ = 114;
v___x_846_ = lean_uint32_dec_eq(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v_source_843_);
lean_dec(v___f_840_);
lean_dec_ref(v_inst_839_);
lean_dec(v___f_838_);
lean_dec(v_toBind_837_);
lean_dec(v_toPure_836_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_apply_2(v___f_835_, v___x_847_, v_start_842_);
return v___x_848_;
}
else
{
lean_object* v___f_849_; lean_object* v_pos_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v___f_835_);
lean_inc(v_toBind_837_);
lean_inc_ref(v_source_843_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_849_, 0, v_source_843_);
lean_closure_set(v___f_849_, 1, v_toPure_836_);
lean_closure_set(v___f_849_, 2, v_toBind_837_);
lean_closure_set(v___f_849_, 3, v___f_838_);
v_pos_850_ = lean_string_utf8_next(v_source_843_, v_start_842_);
lean_dec(v_start_842_);
lean_dec_ref(v_source_843_);
v___x_851_ = l___private_Init_While_0__repeatM_erased___redArg(v_inst_839_, v___f_849_, v_pos_850_);
v___x_852_ = lean_apply_4(v_toBind_837_, lean_box(0), lean_box(0), v___x_851_, v___f_840_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(lean_object* v_inst_853_, lean_object* v_strLit_854_, lean_object* v_text_855_, uint8_t v___x_856_, lean_object* v_p_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_toPure_860_, lean_object* v_toBind_861_, lean_object* v_inst_862_, lean_object* v___f_863_, lean_object* v_env_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___f_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_865_ = lean_box(v___x_856_);
lean_inc_n(v_toBind_861_, 3);
lean_inc_n(v_toPure_860_, 2);
lean_inc_ref(v_inst_859_);
lean_inc_ref_n(v_inst_858_, 3);
lean_inc_ref_n(v_text_855_, 2);
lean_inc_n(v_strLit_854_, 2);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__4___boxed), 12, 11);
lean_closure_set(v___f_866_, 0, v_inst_853_);
lean_closure_set(v___f_866_, 1, v_strLit_854_);
lean_closure_set(v___f_866_, 2, v_text_855_);
lean_closure_set(v___f_866_, 3, v___x_865_);
lean_closure_set(v___f_866_, 4, v_env_864_);
lean_closure_set(v___f_866_, 5, v_p_857_);
lean_closure_set(v___f_866_, 6, v_inst_858_);
lean_closure_set(v___f_866_, 7, v_inst_859_);
lean_closure_set(v___f_866_, 8, v_toPure_860_);
lean_closure_set(v___f_866_, 9, v_toBind_861_);
lean_closure_set(v___f_866_, 10, v_inst_862_);
v___f_867_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__5), 2, 1);
lean_closure_set(v___f_867_, 0, v___f_866_);
lean_inc_ref(v___f_867_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__7___boxed), 10, 8);
lean_closure_set(v___f_868_, 0, v_text_855_);
lean_closure_set(v___f_868_, 1, v_inst_858_);
lean_closure_set(v___f_868_, 2, v_inst_859_);
lean_closure_set(v___f_868_, 3, v_strLit_854_);
lean_closure_set(v___f_868_, 4, v_toBind_861_);
lean_closure_set(v___f_868_, 5, v___f_867_);
lean_closure_set(v___f_868_, 6, v_toPure_860_);
lean_closure_set(v___f_868_, 7, v___f_867_);
lean_inc_ref(v___f_868_);
v___f_869_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__6), 2, 1);
lean_closure_set(v___f_869_, 0, v___f_868_);
v___f_870_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__9), 8, 7);
lean_closure_set(v___f_870_, 0, v_text_855_);
lean_closure_set(v___f_870_, 1, v___f_868_);
lean_closure_set(v___f_870_, 2, v_toPure_860_);
lean_closure_set(v___f_870_, 3, v_toBind_861_);
lean_closure_set(v___f_870_, 4, v___f_863_);
lean_closure_set(v___f_870_, 5, v_inst_858_);
lean_closure_set(v___f_870_, 6, v___f_869_);
v___x_871_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg(v_inst_858_, v_strLit_854_);
lean_dec(v_strLit_854_);
v___x_872_ = lean_apply_4(v_toBind_861_, lean_box(0), lean_box(0), v___x_871_, v___f_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed(lean_object* v_inst_873_, lean_object* v_strLit_874_, lean_object* v_text_875_, lean_object* v___x_876_, lean_object* v_p_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_toPure_880_, lean_object* v_toBind_881_, lean_object* v_inst_882_, lean_object* v___f_883_, lean_object* v_env_884_){
_start:
{
uint8_t v___x_1197__boxed_885_; lean_object* v_res_886_; 
v___x_1197__boxed_885_ = lean_unbox(v___x_876_);
v_res_886_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__10(v_inst_873_, v_strLit_874_, v_text_875_, v___x_1197__boxed_885_, v_p_877_, v_inst_878_, v_inst_879_, v_toPure_880_, v_toBind_881_, v_inst_882_, v___f_883_, v_env_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_strLit_889_, uint8_t v___x_890_, lean_object* v_p_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_toPure_894_, lean_object* v_toBind_895_, lean_object* v_inst_896_, lean_object* v___f_897_, lean_object* v_text_898_){
_start:
{
lean_object* v_getEnv_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; 
v_getEnv_899_ = lean_ctor_get(v_inst_887_, 0);
lean_inc(v_getEnv_899_);
lean_dec_ref(v_inst_887_);
v___x_900_ = lean_box(v___x_890_);
lean_inc(v_toBind_895_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__10___boxed), 12, 11);
lean_closure_set(v___f_901_, 0, v_inst_888_);
lean_closure_set(v___f_901_, 1, v_strLit_889_);
lean_closure_set(v___f_901_, 2, v_text_898_);
lean_closure_set(v___f_901_, 3, v___x_900_);
lean_closure_set(v___f_901_, 4, v_p_891_);
lean_closure_set(v___f_901_, 5, v_inst_892_);
lean_closure_set(v___f_901_, 6, v_inst_893_);
lean_closure_set(v___f_901_, 7, v_toPure_894_);
lean_closure_set(v___f_901_, 8, v_toBind_895_);
lean_closure_set(v___f_901_, 9, v_inst_896_);
lean_closure_set(v___f_901_, 10, v___f_897_);
v___x_902_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v_getEnv_899_, v___f_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed(lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_strLit_905_, lean_object* v___x_906_, lean_object* v_p_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_toPure_910_, lean_object* v_toBind_911_, lean_object* v_inst_912_, lean_object* v___f_913_, lean_object* v_text_914_){
_start:
{
uint8_t v___x_1232__boxed_915_; lean_object* v_res_916_; 
v___x_1232__boxed_915_ = lean_unbox(v___x_906_);
v_res_916_ = l_Lean_Doc_parseQuotedStrLit___redArg___lam__11(v_inst_903_, v_inst_904_, v_strLit_905_, v___x_1232__boxed_915_, v_p_907_, v_inst_908_, v_inst_909_, v_toPure_910_, v_toBind_911_, v_inst_912_, v___f_913_, v_text_914_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit___redArg(lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_p_923_, lean_object* v_strLit_924_){
_start:
{
uint8_t v___x_925_; uint8_t v___y_927_; lean_object* v___x_937_; 
v___x_925_ = 1;
v___x_937_ = l_Lean_Syntax_getPos_x3f(v_strLit_924_, v___x_925_);
if (lean_obj_tag(v___x_937_) == 0)
{
v___y_927_ = v___x_925_;
goto v___jp_926_;
}
else
{
uint8_t v___x_938_; 
lean_dec_ref_known(v___x_937_, 1);
v___x_938_ = 0;
v___y_927_ = v___x_938_;
goto v___jp_926_;
}
v___jp_926_:
{
if (v___y_927_ == 0)
{
lean_object* v_toApplicative_928_; lean_object* v_toBind_929_; lean_object* v_toPure_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___f_933_; lean_object* v___x_934_; 
v_toApplicative_928_ = lean_ctor_get(v_inst_917_, 0);
v_toBind_929_ = lean_ctor_get(v_inst_917_, 1);
lean_inc_n(v_toBind_929_, 2);
v_toPure_930_ = lean_ctor_get(v_toApplicative_928_, 1);
lean_inc_n(v_toPure_930_, 2);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__0), 2, 1);
lean_closure_set(v___f_931_, 0, v_toPure_930_);
v___x_932_ = lean_box(v___x_925_);
v___f_933_ = lean_alloc_closure((void*)(l_Lean_Doc_parseQuotedStrLit___redArg___lam__11___boxed), 12, 11);
lean_closure_set(v___f_933_, 0, v_inst_919_);
lean_closure_set(v___f_933_, 1, v_inst_921_);
lean_closure_set(v___f_933_, 2, v_strLit_924_);
lean_closure_set(v___f_933_, 3, v___x_932_);
lean_closure_set(v___f_933_, 4, v_p_923_);
lean_closure_set(v___f_933_, 5, v_inst_917_);
lean_closure_set(v___f_933_, 6, v_inst_920_);
lean_closure_set(v___f_933_, 7, v_toPure_930_);
lean_closure_set(v___f_933_, 8, v_toBind_929_);
lean_closure_set(v___f_933_, 9, v_inst_922_);
lean_closure_set(v___f_933_, 10, v___f_931_);
v___x_934_ = lean_apply_4(v_toBind_929_, lean_box(0), lean_box(0), v_inst_918_, v___f_933_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v_inst_918_);
v___x_935_ = l_Lean_TSyntax_getString(v_strLit_924_);
lean_dec(v_strLit_924_);
v___x_936_ = l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg(v_inst_917_, v_inst_919_, v_inst_920_, v_inst_921_, v_inst_922_, v_p_923_, v___x_935_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseQuotedStrLit(lean_object* v_m_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_inst_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_p_946_, lean_object* v_strLit_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Doc_parseQuotedStrLit___redArg(v_inst_940_, v_inst_941_, v_inst_942_, v_inst_943_, v_inst_944_, v_inst_945_, v_p_946_, v_strLit_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0(lean_object* v_s_949_, lean_object* v_toPure_950_, uint8_t v_err_951_){
_start:
{
lean_object* v_stxStack_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_stxStack_952_ = lean_ctor_get(v_s_949_, 0);
v___x_953_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_952_);
v___x_954_ = lean_box(v_err_951_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_apply_2(v_toPure_950_, lean_box(0), v___x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed(lean_object* v_s_957_, lean_object* v_toPure_958_, lean_object* v_err_959_){
_start:
{
uint8_t v_err_boxed_960_; lean_object* v_res_961_; 
v_err_boxed_960_ = lean_unbox(v_err_959_);
v_res_961_ = l_Lean_Doc_parseContent_x27___redArg___lam__0(v_s_957_, v_toPure_958_, v_err_boxed_960_);
lean_dec_ref(v_s_957_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1(lean_object* v___f_962_, uint8_t v_err_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_box(v_err_963_);
v___x_965_ = lean_apply_1(v___f_962_, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed(lean_object* v___f_966_, lean_object* v_err_967_){
_start:
{
uint8_t v_err_boxed_968_; lean_object* v_res_969_; 
v_err_boxed_968_ = lean_unbox(v_err_967_);
v_res_969_ = l_Lean_Doc_parseContent_x27___redArg___lam__1(v___f_966_, v_err_boxed_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2(lean_object* v_toPure_970_, uint8_t v___x_971_, lean_object* v_toBind_972_, lean_object* v___f_973_, lean_object* v_____r_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_box(v___x_971_);
v___x_976_ = lean_apply_2(v_toPure_970_, lean_box(0), v___x_975_);
v___x_977_ = lean_apply_4(v_toBind_972_, lean_box(0), lean_box(0), v___x_976_, v___f_973_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed(lean_object* v_toPure_978_, lean_object* v___x_979_, lean_object* v_toBind_980_, lean_object* v___f_981_, lean_object* v_____r_982_){
_start:
{
uint8_t v___x_790__boxed_983_; lean_object* v_res_984_; 
v___x_790__boxed_983_ = lean_unbox(v___x_979_);
v_res_984_ = l_Lean_Doc_parseContent_x27___redArg___lam__2(v_toPure_978_, v___x_790__boxed_983_, v_toBind_980_, v___f_981_, v_____r_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6(lean_object* v_env_985_, lean_object* v_p_986_, lean_object* v_ictx_987_, lean_object* v_s_988_, lean_object* v_toPure_989_, uint8_t v___x_990_, lean_object* v_toBind_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_inst_995_, uint8_t v___y_996_, lean_object* v_____do__lift_997_){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_s_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_998_ = lean_box(0);
v___x_999_ = lean_box(0);
lean_inc_ref(v_env_985_);
v___x_1000_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1000_, 0, v_env_985_);
lean_ctor_set(v___x_1000_, 1, v_____do__lift_997_);
lean_ctor_set(v___x_1000_, 2, v___x_998_);
lean_ctor_set(v___x_1000_, 3, v___x_999_);
v___x_1001_ = l_Lean_Parser_getTokenTable(v_env_985_);
lean_inc_ref(v_ictx_987_);
v_s_1002_ = l_Lean_Parser_ParserFn_run(v_p_986_, v_ictx_987_, v___x_1000_, v___x_1001_, v_s_988_);
lean_inc(v_toPure_989_);
lean_inc_ref_n(v_s_1002_, 2);
v___f_1003_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1003_, 0, v_s_1002_);
lean_closure_set(v___f_1003_, 1, v_toPure_989_);
v___x_1004_ = l_Lean_Parser_ParserState_allErrors(v_s_1002_);
v___x_1005_ = lean_array_get_size(v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_nat_dec_eq(v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___f_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1008_, 0, v___f_1003_);
v___x_1009_ = lean_box(v___x_990_);
lean_inc(v_toBind_991_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1010_, 0, v_toPure_989_);
lean_closure_set(v___f_1010_, 1, v___x_1009_);
lean_closure_set(v___f_1010_, 2, v_toBind_991_);
lean_closure_set(v___f_1010_, 3, v___f_1008_);
v___x_1011_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_987_, v_s_1002_);
v___x_1012_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = l_Lean_MessageData_ofFormat(v___x_1012_);
v___x_1014_ = l_Lean_logError___redArg(v_inst_992_, v_inst_993_, v_inst_994_, v_inst_995_, v___x_1013_);
v___x_1015_ = lean_apply_4(v_toBind_991_, lean_box(0), lean_box(0), v___x_1014_, v___f_1010_);
return v___x_1015_;
}
else
{
lean_object* v_pos_1016_; uint8_t v___x_1017_; 
v_pos_1016_ = lean_ctor_get(v_s_1002_, 2);
lean_inc(v_pos_1016_);
v___x_1017_ = l_Lean_Parser_InputContext_atEnd(v_ictx_987_, v_pos_1016_);
lean_dec(v_pos_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___f_1018_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1018_, 0, v___f_1003_);
v___x_1019_ = lean_box(v___x_990_);
lean_inc(v_toBind_991_);
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1020_, 0, v_toPure_989_);
lean_closure_set(v___f_1020_, 1, v___x_1019_);
lean_closure_set(v___f_1020_, 2, v_toBind_991_);
lean_closure_set(v___f_1020_, 3, v___f_1018_);
v___x_1021_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1022_ = l_Lean_Parser_ParserState_mkError(v_s_1002_, v___x_1021_);
v___x_1023_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_987_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = l_Lean_MessageData_ofFormat(v___x_1024_);
v___x_1026_ = l_Lean_logError___redArg(v_inst_992_, v_inst_993_, v_inst_994_, v_inst_995_, v___x_1025_);
v___x_1027_ = lean_apply_4(v_toBind_991_, lean_box(0), lean_box(0), v___x_1026_, v___f_1020_);
return v___x_1027_;
}
else
{
lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec_ref(v_s_1002_);
lean_dec(v_inst_995_);
lean_dec(v_inst_994_);
lean_dec_ref(v_inst_993_);
lean_dec_ref(v_inst_992_);
lean_dec_ref(v_ictx_987_);
v___f_1028_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1028_, 0, v___f_1003_);
v___x_1029_ = lean_box(v___y_996_);
v___x_1030_ = lean_apply_2(v_toPure_989_, lean_box(0), v___x_1029_);
v___x_1031_ = lean_apply_4(v_toBind_991_, lean_box(0), lean_box(0), v___x_1030_, v___f_1028_);
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed(lean_object* v_env_1032_, lean_object* v_p_1033_, lean_object* v_ictx_1034_, lean_object* v_s_1035_, lean_object* v_toPure_1036_, lean_object* v___x_1037_, lean_object* v_toBind_1038_, lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v___y_1043_, lean_object* v_____do__lift_1044_){
_start:
{
uint8_t v___x_806__boxed_1045_; uint8_t v___y_811__boxed_1046_; lean_object* v_res_1047_; 
v___x_806__boxed_1045_ = lean_unbox(v___x_1037_);
v___y_811__boxed_1046_ = lean_unbox(v___y_1043_);
v_res_1047_ = l_Lean_Doc_parseContent_x27___redArg___lam__6(v_env_1032_, v_p_1033_, v_ictx_1034_, v_s_1035_, v_toPure_1036_, v___x_806__boxed_1045_, v_toBind_1038_, v_inst_1039_, v_inst_1040_, v_inst_1041_, v_inst_1042_, v___y_811__boxed_1046_, v_____do__lift_1044_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3(lean_object* v_source_1048_, uint8_t v___x_1049_, lean_object* v___y_1050_, lean_object* v_env_1051_, lean_object* v_p_1052_, lean_object* v_toPure_1053_, lean_object* v_toBind_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_inst_1058_, uint8_t v___y_1059_, lean_object* v_tok_1060_, lean_object* v___x_1061_, lean_object* v_____do__lift_1062_){
_start:
{
lean_object* v_ictx_1063_; lean_object* v___x_1064_; lean_object* v___y_1066_; lean_object* v___x_1072_; 
lean_inc_ref(v_source_1048_);
v_ictx_1063_ = l_Lean_Parser_mkInputContext___redArg(v_source_1048_, v_____do__lift_1062_, v___x_1049_, v___y_1050_);
v___x_1064_ = l_Lean_Parser_mkParserState(v_source_1048_);
lean_dec_ref(v_source_1048_);
v___x_1072_ = l_Lean_Syntax_getPos_x3f(v_tok_1060_, v___x_1049_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1074_ = l_panic___redArg(v___x_1061_, v___x_1073_);
v___y_1066_ = v___x_1074_;
goto v___jp_1065_;
}
else
{
lean_object* v_val_1075_; 
v_val_1075_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_val_1075_);
lean_dec_ref_known(v___x_1072_, 1);
v___y_1066_ = v_val_1075_;
goto v___jp_1065_;
}
v___jp_1065_:
{
lean_object* v_s_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; 
v_s_1067_ = l_Lean_Parser_ParserState_setPos(v___x_1064_, v___y_1066_);
v___x_1068_ = lean_box(v___x_1049_);
v___x_1069_ = lean_box(v___y_1059_);
lean_inc(v_inst_1058_);
lean_inc(v_toBind_1054_);
v___f_1070_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1070_, 0, v_env_1051_);
lean_closure_set(v___f_1070_, 1, v_p_1052_);
lean_closure_set(v___f_1070_, 2, v_ictx_1063_);
lean_closure_set(v___f_1070_, 3, v_s_1067_);
lean_closure_set(v___f_1070_, 4, v_toPure_1053_);
lean_closure_set(v___f_1070_, 5, v___x_1068_);
lean_closure_set(v___f_1070_, 6, v_toBind_1054_);
lean_closure_set(v___f_1070_, 7, v_inst_1055_);
lean_closure_set(v___f_1070_, 8, v_inst_1056_);
lean_closure_set(v___f_1070_, 9, v_inst_1057_);
lean_closure_set(v___f_1070_, 10, v_inst_1058_);
lean_closure_set(v___f_1070_, 11, v___x_1069_);
v___x_1071_ = lean_apply_4(v_toBind_1054_, lean_box(0), lean_box(0), v_inst_1058_, v___f_1070_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed(lean_object* v_source_1076_, lean_object* v___x_1077_, lean_object* v___y_1078_, lean_object* v_env_1079_, lean_object* v_p_1080_, lean_object* v_toPure_1081_, lean_object* v_toBind_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v___y_1087_, lean_object* v_tok_1088_, lean_object* v___x_1089_, lean_object* v_____do__lift_1090_){
_start:
{
uint8_t v___x_900__boxed_1091_; uint8_t v___y_906__boxed_1092_; lean_object* v_res_1093_; 
v___x_900__boxed_1091_ = lean_unbox(v___x_1077_);
v___y_906__boxed_1092_ = lean_unbox(v___y_1087_);
v_res_1093_ = l_Lean_Doc_parseContent_x27___redArg___lam__3(v_source_1076_, v___x_900__boxed_1091_, v___y_1078_, v_env_1079_, v_p_1080_, v_toPure_1081_, v_toBind_1082_, v_inst_1083_, v_inst_1084_, v_inst_1085_, v_inst_1086_, v___y_906__boxed_1092_, v_tok_1088_, v___x_1089_, v_____do__lift_1090_);
lean_dec(v___x_1089_);
lean_dec(v_tok_1088_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4(lean_object* v_text_1094_, lean_object* v_inst_1095_, uint8_t v___x_1096_, lean_object* v_p_1097_, lean_object* v_toPure_1098_, lean_object* v_toBind_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, uint8_t v___y_1103_, lean_object* v_tok_1104_, lean_object* v___x_1105_, lean_object* v_env_1106_){
_start:
{
lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1116_; lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_Syntax_getTailPos_x3f(v_tok_1104_, v___x_1096_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_obj_once(&l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3, &l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3_once, _init_l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_strLitRange___redArg___closed__3);
v___x_1122_ = l_panic___redArg(v___x_1105_, v___x_1121_);
v___y_1116_ = v___x_1122_;
goto v___jp_1115_;
}
else
{
lean_object* v_val_1123_; 
v_val_1123_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_val_1123_);
lean_dec_ref_known(v___x_1120_, 1);
v___y_1116_ = v_val_1123_;
goto v___jp_1115_;
}
v___jp_1107_:
{
lean_object* v_getFileName_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; 
v_getFileName_1110_ = lean_ctor_get(v_inst_1095_, 2);
lean_inc(v_getFileName_1110_);
v___x_1111_ = lean_box(v___x_1096_);
v___x_1112_ = lean_box(v___y_1103_);
lean_inc(v_toBind_1099_);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1113_, 0, v___y_1108_);
lean_closure_set(v___f_1113_, 1, v___x_1111_);
lean_closure_set(v___f_1113_, 2, v___y_1109_);
lean_closure_set(v___f_1113_, 3, v_env_1106_);
lean_closure_set(v___f_1113_, 4, v_p_1097_);
lean_closure_set(v___f_1113_, 5, v_toPure_1098_);
lean_closure_set(v___f_1113_, 6, v_toBind_1099_);
lean_closure_set(v___f_1113_, 7, v_inst_1100_);
lean_closure_set(v___f_1113_, 8, v_inst_1095_);
lean_closure_set(v___f_1113_, 9, v_inst_1101_);
lean_closure_set(v___f_1113_, 10, v_inst_1102_);
lean_closure_set(v___f_1113_, 11, v___x_1112_);
lean_closure_set(v___f_1113_, 12, v_tok_1104_);
lean_closure_set(v___f_1113_, 13, v___x_1105_);
v___x_1114_ = lean_apply_4(v_toBind_1099_, lean_box(0), lean_box(0), v_getFileName_1110_, v___f_1113_);
return v___x_1114_;
}
v___jp_1115_:
{
lean_object* v_source_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_source_1117_ = lean_ctor_get(v_text_1094_, 0);
lean_inc_ref(v_source_1117_);
lean_dec_ref(v_text_1094_);
v___x_1118_ = lean_string_utf8_byte_size(v_source_1117_);
v___x_1119_ = lean_nat_dec_le(v___y_1116_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v___y_1116_);
v___y_1108_ = v_source_1117_;
v___y_1109_ = v___x_1118_;
goto v___jp_1107_;
}
else
{
v___y_1108_ = v_source_1117_;
v___y_1109_ = v___y_1116_;
goto v___jp_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed(lean_object* v_text_1124_, lean_object* v_inst_1125_, lean_object* v___x_1126_, lean_object* v_p_1127_, lean_object* v_toPure_1128_, lean_object* v_toBind_1129_, lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v___y_1133_, lean_object* v_tok_1134_, lean_object* v___x_1135_, lean_object* v_env_1136_){
_start:
{
uint8_t v___x_965__boxed_1137_; uint8_t v___y_969__boxed_1138_; lean_object* v_res_1139_; 
v___x_965__boxed_1137_ = lean_unbox(v___x_1126_);
v___y_969__boxed_1138_ = lean_unbox(v___y_1133_);
v_res_1139_ = l_Lean_Doc_parseContent_x27___redArg___lam__4(v_text_1124_, v_inst_1125_, v___x_965__boxed_1137_, v_p_1127_, v_toPure_1128_, v_toBind_1129_, v_inst_1130_, v_inst_1131_, v_inst_1132_, v___y_969__boxed_1138_, v_tok_1134_, v___x_1135_, v_env_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5(lean_object* v_inst_1140_, lean_object* v_inst_1141_, uint8_t v___x_1142_, lean_object* v_p_1143_, lean_object* v_toPure_1144_, lean_object* v_toBind_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_inst_1148_, uint8_t v___y_1149_, lean_object* v_tok_1150_, lean_object* v___x_1151_, lean_object* v_text_1152_){
_start:
{
lean_object* v_getEnv_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; 
v_getEnv_1153_ = lean_ctor_get(v_inst_1140_, 0);
lean_inc(v_getEnv_1153_);
lean_dec_ref(v_inst_1140_);
v___x_1154_ = lean_box(v___x_1142_);
v___x_1155_ = lean_box(v___y_1149_);
lean_inc(v_toBind_1145_);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__4___boxed), 13, 12);
lean_closure_set(v___f_1156_, 0, v_text_1152_);
lean_closure_set(v___f_1156_, 1, v_inst_1141_);
lean_closure_set(v___f_1156_, 2, v___x_1154_);
lean_closure_set(v___f_1156_, 3, v_p_1143_);
lean_closure_set(v___f_1156_, 4, v_toPure_1144_);
lean_closure_set(v___f_1156_, 5, v_toBind_1145_);
lean_closure_set(v___f_1156_, 6, v_inst_1146_);
lean_closure_set(v___f_1156_, 7, v_inst_1147_);
lean_closure_set(v___f_1156_, 8, v_inst_1148_);
lean_closure_set(v___f_1156_, 9, v___x_1155_);
lean_closure_set(v___f_1156_, 10, v_tok_1150_);
lean_closure_set(v___f_1156_, 11, v___x_1151_);
v___x_1157_ = lean_apply_4(v_toBind_1145_, lean_box(0), lean_box(0), v_getEnv_1153_, v___f_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed(lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v___x_1160_, lean_object* v_p_1161_, lean_object* v_toPure_1162_, lean_object* v_toBind_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v___y_1167_, lean_object* v_tok_1168_, lean_object* v___x_1169_, lean_object* v_text_1170_){
_start:
{
uint8_t v___x_1022__boxed_1171_; uint8_t v___y_1026__boxed_1172_; lean_object* v_res_1173_; 
v___x_1022__boxed_1171_ = lean_unbox(v___x_1160_);
v___y_1026__boxed_1172_ = lean_unbox(v___y_1167_);
v_res_1173_ = l_Lean_Doc_parseContent_x27___redArg___lam__5(v_inst_1158_, v_inst_1159_, v___x_1022__boxed_1171_, v_p_1161_, v_toPure_1162_, v_toBind_1163_, v_inst_1164_, v_inst_1165_, v_inst_1166_, v___y_1026__boxed_1172_, v_tok_1168_, v___x_1169_, v_text_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7(lean_object* v_st_1174_, lean_object* v_toPure_1175_, uint8_t v_err_1176_){
_start:
{
lean_object* v_stxStack_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_stxStack_1177_ = lean_ctor_get(v_st_1174_, 0);
v___x_1178_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1177_);
v___x_1179_ = lean_box(v_err_1176_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_apply_2(v_toPure_1175_, lean_box(0), v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed(lean_object* v_st_1182_, lean_object* v_toPure_1183_, lean_object* v_err_1184_){
_start:
{
uint8_t v_err_boxed_1185_; lean_object* v_res_1186_; 
v_err_boxed_1185_ = lean_unbox(v_err_1184_);
v_res_1186_ = l_Lean_Doc_parseContent_x27___redArg___lam__7(v_st_1182_, v_toPure_1183_, v_err_boxed_1185_);
lean_dec_ref(v_st_1182_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13(lean_object* v_env_1187_, lean_object* v_contents_1188_, lean_object* v_p_1189_, lean_object* v_ictx_1190_, lean_object* v_toPure_1191_, uint8_t v___x_1192_, lean_object* v_toBind_1193_, lean_object* v_inst_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_____do__lift_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_st_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_box(0);
lean_inc_ref(v_env_1187_);
v___x_1201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1201_, 0, v_env_1187_);
lean_ctor_set(v___x_1201_, 1, v_____do__lift_1198_);
lean_ctor_set(v___x_1201_, 2, v___x_1199_);
lean_ctor_set(v___x_1201_, 3, v___x_1200_);
v___x_1202_ = l_Lean_Parser_getTokenTable(v_env_1187_);
v___x_1203_ = l_Lean_Parser_mkParserState(v_contents_1188_);
lean_inc_ref(v_ictx_1190_);
v_st_1204_ = l_Lean_Parser_ParserFn_run(v_p_1189_, v_ictx_1190_, v___x_1201_, v___x_1202_, v___x_1203_);
lean_inc(v_toPure_1191_);
lean_inc_ref_n(v_st_1204_, 2);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_1205_, 0, v_st_1204_);
lean_closure_set(v___f_1205_, 1, v_toPure_1191_);
v___x_1206_ = l_Lean_Parser_ParserState_allErrors(v_st_1204_);
v___x_1207_ = lean_array_get_size(v___x_1206_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_nat_dec_eq(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___f_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___f_1210_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1210_, 0, v___f_1205_);
v___x_1211_ = lean_box(v___x_1192_);
lean_inc(v_toBind_1193_);
v___f_1212_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1212_, 0, v_toPure_1191_);
lean_closure_set(v___f_1212_, 1, v___x_1211_);
lean_closure_set(v___f_1212_, 2, v_toBind_1193_);
lean_closure_set(v___f_1212_, 3, v___f_1210_);
v___x_1213_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1190_, v_st_1204_);
v___x_1214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
v___x_1215_ = l_Lean_MessageData_ofFormat(v___x_1214_);
v___x_1216_ = l_Lean_logError___redArg(v_inst_1194_, v_inst_1195_, v_inst_1196_, v_inst_1197_, v___x_1215_);
v___x_1217_ = lean_apply_4(v_toBind_1193_, lean_box(0), lean_box(0), v___x_1216_, v___f_1212_);
return v___x_1217_;
}
else
{
lean_object* v_pos_1218_; uint8_t v___x_1219_; 
v_pos_1218_ = lean_ctor_get(v_st_1204_, 2);
lean_inc(v_pos_1218_);
v___x_1219_ = l_Lean_Parser_InputContext_atEnd(v_ictx_1190_, v_pos_1218_);
lean_dec(v_pos_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1220_, 0, v___f_1205_);
v___x_1221_ = lean_box(v___x_1192_);
lean_inc(v_toBind_1193_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__2___boxed), 5, 4);
lean_closure_set(v___f_1222_, 0, v_toPure_1191_);
lean_closure_set(v___f_1222_, 1, v___x_1221_);
lean_closure_set(v___f_1222_, 2, v_toBind_1193_);
lean_closure_set(v___f_1222_, 3, v___f_1220_);
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_DocString_Builtin_Parsing_0__Lean_Doc_parseFromContents___redArg___lam__0___closed__0));
v___x_1224_ = l_Lean_Parser_ParserState_mkError(v_st_1204_, v___x_1223_);
v___x_1225_ = l_Lean_Parser_ParserState_toErrorMsg(v_ictx_1190_, v___x_1224_);
v___x_1226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
v___x_1227_ = l_Lean_MessageData_ofFormat(v___x_1226_);
v___x_1228_ = l_Lean_logError___redArg(v_inst_1194_, v_inst_1195_, v_inst_1196_, v_inst_1197_, v___x_1227_);
v___x_1229_ = lean_apply_4(v_toBind_1193_, lean_box(0), lean_box(0), v___x_1228_, v___f_1222_);
return v___x_1229_;
}
else
{
lean_object* v___f_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec_ref(v_st_1204_);
lean_dec(v_inst_1197_);
lean_dec(v_inst_1196_);
lean_dec_ref(v_inst_1195_);
lean_dec_ref(v_inst_1194_);
lean_dec_ref(v_ictx_1190_);
v___f_1230_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1230_, 0, v___f_1205_);
v___x_1231_ = 0;
v___x_1232_ = lean_box(v___x_1231_);
v___x_1233_ = lean_apply_2(v_toPure_1191_, lean_box(0), v___x_1232_);
v___x_1234_ = lean_apply_4(v_toBind_1193_, lean_box(0), lean_box(0), v___x_1233_, v___f_1230_);
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed(lean_object* v_env_1235_, lean_object* v_contents_1236_, lean_object* v_p_1237_, lean_object* v_ictx_1238_, lean_object* v_toPure_1239_, lean_object* v___x_1240_, lean_object* v_toBind_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_____do__lift_1246_){
_start:
{
uint8_t v___x_1061__boxed_1247_; lean_object* v_res_1248_; 
v___x_1061__boxed_1247_ = lean_unbox(v___x_1240_);
v_res_1248_ = l_Lean_Doc_parseContent_x27___redArg___lam__13(v_env_1235_, v_contents_1236_, v_p_1237_, v_ictx_1238_, v_toPure_1239_, v___x_1061__boxed_1247_, v_toBind_1241_, v_inst_1242_, v_inst_1243_, v_inst_1244_, v_inst_1245_, v_____do__lift_1246_);
lean_dec_ref(v_contents_1236_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8(lean_object* v_contents_1249_, uint8_t v___x_1250_, lean_object* v_env_1251_, lean_object* v_p_1252_, lean_object* v_toPure_1253_, lean_object* v_toBind_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_____do__lift_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v_ictx_1261_; lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; 
v___x_1260_ = lean_string_utf8_byte_size(v_contents_1249_);
lean_inc_ref(v_contents_1249_);
v_ictx_1261_ = l_Lean_Parser_mkInputContext___redArg(v_contents_1249_, v_____do__lift_1259_, v___x_1250_, v___x_1260_);
v___x_1262_ = lean_box(v___x_1250_);
lean_inc(v_inst_1258_);
lean_inc(v_toBind_1254_);
v___f_1263_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__13___boxed), 12, 11);
lean_closure_set(v___f_1263_, 0, v_env_1251_);
lean_closure_set(v___f_1263_, 1, v_contents_1249_);
lean_closure_set(v___f_1263_, 2, v_p_1252_);
lean_closure_set(v___f_1263_, 3, v_ictx_1261_);
lean_closure_set(v___f_1263_, 4, v_toPure_1253_);
lean_closure_set(v___f_1263_, 5, v___x_1262_);
lean_closure_set(v___f_1263_, 6, v_toBind_1254_);
lean_closure_set(v___f_1263_, 7, v_inst_1255_);
lean_closure_set(v___f_1263_, 8, v_inst_1256_);
lean_closure_set(v___f_1263_, 9, v_inst_1257_);
lean_closure_set(v___f_1263_, 10, v_inst_1258_);
v___x_1264_ = lean_apply_4(v_toBind_1254_, lean_box(0), lean_box(0), v_inst_1258_, v___f_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed(lean_object* v_contents_1265_, lean_object* v___x_1266_, lean_object* v_env_1267_, lean_object* v_p_1268_, lean_object* v_toPure_1269_, lean_object* v_toBind_1270_, lean_object* v_inst_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_____do__lift_1275_){
_start:
{
uint8_t v___x_1147__boxed_1276_; lean_object* v_res_1277_; 
v___x_1147__boxed_1276_ = lean_unbox(v___x_1266_);
v_res_1277_ = l_Lean_Doc_parseContent_x27___redArg___lam__8(v_contents_1265_, v___x_1147__boxed_1276_, v_env_1267_, v_p_1268_, v_toPure_1269_, v_toBind_1270_, v_inst_1271_, v_inst_1272_, v_inst_1273_, v_inst_1274_, v_____do__lift_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9(lean_object* v_inst_1278_, lean_object* v_contents_1279_, uint8_t v___x_1280_, lean_object* v_p_1281_, lean_object* v_toPure_1282_, lean_object* v_toBind_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_env_1287_){
_start:
{
lean_object* v_getFileName_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___x_1291_; 
v_getFileName_1288_ = lean_ctor_get(v_inst_1278_, 2);
lean_inc(v_getFileName_1288_);
v___x_1289_ = lean_box(v___x_1280_);
lean_inc(v_toBind_1283_);
v___f_1290_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_1290_, 0, v_contents_1279_);
lean_closure_set(v___f_1290_, 1, v___x_1289_);
lean_closure_set(v___f_1290_, 2, v_env_1287_);
lean_closure_set(v___f_1290_, 3, v_p_1281_);
lean_closure_set(v___f_1290_, 4, v_toPure_1282_);
lean_closure_set(v___f_1290_, 5, v_toBind_1283_);
lean_closure_set(v___f_1290_, 6, v_inst_1284_);
lean_closure_set(v___f_1290_, 7, v_inst_1278_);
lean_closure_set(v___f_1290_, 8, v_inst_1285_);
lean_closure_set(v___f_1290_, 9, v_inst_1286_);
v___x_1291_ = lean_apply_4(v_toBind_1283_, lean_box(0), lean_box(0), v_getFileName_1288_, v___f_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed(lean_object* v_inst_1292_, lean_object* v_contents_1293_, lean_object* v___x_1294_, lean_object* v_p_1295_, lean_object* v_toPure_1296_, lean_object* v_toBind_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_env_1301_){
_start:
{
uint8_t v___x_1174__boxed_1302_; lean_object* v_res_1303_; 
v___x_1174__boxed_1302_ = lean_unbox(v___x_1294_);
v_res_1303_ = l_Lean_Doc_parseContent_x27___redArg___lam__9(v_inst_1292_, v_contents_1293_, v___x_1174__boxed_1302_, v_p_1295_, v_toPure_1296_, v_toBind_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_, v_env_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27___redArg(lean_object* v_inst_1304_, lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_p_1310_, lean_object* v_tok_1311_, lean_object* v_contents_1312_){
_start:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; uint8_t v___y_1316_; lean_object* v___x_1331_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = 1;
v___x_1331_ = l_Lean_Syntax_getPos_x3f(v_tok_1311_, v___x_1314_);
if (lean_obj_tag(v___x_1331_) == 0)
{
v___y_1316_ = v___x_1314_;
goto v___jp_1315_;
}
else
{
uint8_t v___x_1332_; 
lean_dec_ref_known(v___x_1331_, 1);
v___x_1332_ = 0;
v___y_1316_ = v___x_1332_;
goto v___jp_1315_;
}
v___jp_1315_:
{
if (v___y_1316_ == 0)
{
lean_object* v_toApplicative_1317_; lean_object* v_toBind_1318_; lean_object* v_toPure_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; 
v_toApplicative_1317_ = lean_ctor_get(v_inst_1304_, 0);
lean_dec_ref(v_contents_1312_);
v_toBind_1318_ = lean_ctor_get(v_inst_1304_, 1);
lean_inc_n(v_toBind_1318_, 2);
v_toPure_1319_ = lean_ctor_get(v_toApplicative_1317_, 1);
lean_inc(v_toPure_1319_);
v___x_1320_ = lean_box(v___x_1314_);
v___x_1321_ = lean_box(v___y_1316_);
v___f_1322_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_1322_, 0, v_inst_1306_);
lean_closure_set(v___f_1322_, 1, v_inst_1308_);
lean_closure_set(v___f_1322_, 2, v___x_1320_);
lean_closure_set(v___f_1322_, 3, v_p_1310_);
lean_closure_set(v___f_1322_, 4, v_toPure_1319_);
lean_closure_set(v___f_1322_, 5, v_toBind_1318_);
lean_closure_set(v___f_1322_, 6, v_inst_1304_);
lean_closure_set(v___f_1322_, 7, v_inst_1307_);
lean_closure_set(v___f_1322_, 8, v_inst_1309_);
lean_closure_set(v___f_1322_, 9, v___x_1321_);
lean_closure_set(v___f_1322_, 10, v_tok_1311_);
lean_closure_set(v___f_1322_, 11, v___x_1313_);
v___x_1323_ = lean_apply_4(v_toBind_1318_, lean_box(0), lean_box(0), v_inst_1305_, v___f_1322_);
return v___x_1323_;
}
else
{
lean_object* v_toApplicative_1324_; lean_object* v_toBind_1325_; lean_object* v_toPure_1326_; lean_object* v_getEnv_1327_; lean_object* v___x_1328_; lean_object* v___f_1329_; lean_object* v___x_1330_; 
v_toApplicative_1324_ = lean_ctor_get(v_inst_1304_, 0);
lean_dec(v_tok_1311_);
lean_dec(v_inst_1305_);
v_toBind_1325_ = lean_ctor_get(v_inst_1304_, 1);
lean_inc_n(v_toBind_1325_, 2);
v_toPure_1326_ = lean_ctor_get(v_toApplicative_1324_, 1);
lean_inc(v_toPure_1326_);
v_getEnv_1327_ = lean_ctor_get(v_inst_1306_, 0);
lean_inc(v_getEnv_1327_);
lean_dec_ref(v_inst_1306_);
v___x_1328_ = lean_box(v___x_1314_);
v___f_1329_ = lean_alloc_closure((void*)(l_Lean_Doc_parseContent_x27___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1329_, 0, v_inst_1308_);
lean_closure_set(v___f_1329_, 1, v_contents_1312_);
lean_closure_set(v___f_1329_, 2, v___x_1328_);
lean_closure_set(v___f_1329_, 3, v_p_1310_);
lean_closure_set(v___f_1329_, 4, v_toPure_1326_);
lean_closure_set(v___f_1329_, 5, v_toBind_1325_);
lean_closure_set(v___f_1329_, 6, v_inst_1304_);
lean_closure_set(v___f_1329_, 7, v_inst_1307_);
lean_closure_set(v___f_1329_, 8, v_inst_1309_);
v___x_1330_ = lean_apply_4(v_toBind_1325_, lean_box(0), lean_box(0), v_getEnv_1327_, v___f_1329_);
return v___x_1330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseContent_x27(lean_object* v_m_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_p_1340_, lean_object* v_tok_1341_, lean_object* v_contents_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_p_1340_, v_tok_1341_, v_contents_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode___redArg(lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_inst_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_, lean_object* v_p_1350_, lean_object* v_c_1351_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = l_Lean_TSyntax_getVersoCode(v_c_1351_);
v___x_1353_ = l_Lean_Doc_parseContent___redArg(v_inst_1344_, v_inst_1345_, v_inst_1346_, v_inst_1347_, v_inst_1348_, v_inst_1349_, v_p_1350_, v_c_1351_, v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode(lean_object* v_m_1354_, lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_p_1361_, lean_object* v_c_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Doc_parseVersoCode___redArg(v_inst_1355_, v_inst_1356_, v_inst_1357_, v_inst_1358_, v_inst_1359_, v_inst_1360_, v_p_1361_, v_c_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock___redArg(lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_p_1370_, lean_object* v_c_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = l_Lean_TSyntax_getVersoCodeBlock(v_c_1371_);
v___x_1373_ = l_Lean_Doc_parseContent___redArg(v_inst_1364_, v_inst_1365_, v_inst_1366_, v_inst_1367_, v_inst_1368_, v_inst_1369_, v_p_1370_, v_c_1371_, v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCodeBlock(lean_object* v_m_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_p_1381_, lean_object* v_c_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Doc_parseVersoCodeBlock___redArg(v_inst_1375_, v_inst_1376_, v_inst_1377_, v_inst_1378_, v_inst_1379_, v_inst_1380_, v_p_1381_, v_c_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27___redArg(lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_inst_1389_, lean_object* v_p_1390_, lean_object* v_c_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = l_Lean_TSyntax_getVersoCode(v_c_1391_);
v___x_1393_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1384_, v_inst_1385_, v_inst_1386_, v_inst_1387_, v_inst_1388_, v_inst_1389_, v_p_1390_, v_c_1391_, v___x_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseVersoCode_x27(lean_object* v_m_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_p_1401_, lean_object* v_c_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_Doc_parseVersoCode_x27___redArg(v_inst_1395_, v_inst_1396_, v_inst_1397_, v_inst_1398_, v_inst_1399_, v_inst_1400_, v_p_1401_, v_c_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit___redArg(lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_p_1410_, lean_object* v_s_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = l_Lean_TSyntax_getString(v_s_1411_);
v___x_1413_ = l_Lean_Doc_parseContent___redArg(v_inst_1404_, v_inst_1405_, v_inst_1406_, v_inst_1407_, v_inst_1408_, v_inst_1409_, v_p_1410_, v_s_1411_, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit(lean_object* v_m_1414_, lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_inst_1420_, lean_object* v_p_1421_, lean_object* v_s_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Doc_parseStrLit___redArg(v_inst_1415_, v_inst_1416_, v_inst_1417_, v_inst_1418_, v_inst_1419_, v_inst_1420_, v_p_1421_, v_s_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27___redArg(lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_p_1430_, lean_object* v_s_1431_){
_start:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1432_ = l_Lean_TSyntax_getString(v_s_1431_);
v___x_1433_ = l_Lean_Doc_parseContent_x27___redArg(v_inst_1424_, v_inst_1425_, v_inst_1426_, v_inst_1427_, v_inst_1428_, v_inst_1429_, v_p_1430_, v_s_1431_, v___x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_parseStrLit_x27(lean_object* v_m_1434_, lean_object* v_inst_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_p_1441_, lean_object* v_s_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Doc_parseStrLit_x27___redArg(v_inst_1435_, v_inst_1436_, v_inst_1437_, v_inst_1438_, v_inst_1439_, v_inst_1440_, v_p_1441_, v_s_1442_);
return v___x_1443_;
}
}
lean_object* runtime_initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Extension(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DocString_Builtin_Parsing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DocString_Builtin_Parsing(builtin);
}
#ifdef __cplusplus
}
#endif

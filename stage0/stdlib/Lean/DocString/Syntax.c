// Lean compiler output
// Module: Lean.DocString.Syntax
// Imports: public import Lean.Parser.Term.Basic public meta import Lean.Parser.Term.Basic
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
extern lean_object* l_Lean_Parser_ident;
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_numLit;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
extern lean_object* l_Lean_Parser_Term_structInstField;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstField_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__2_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_val"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 154, 240, 169, 25, 100, 158, 173)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(21, 43, 204, 27, 49, 138, 49, 195)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__6_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "`(arg_val| "};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__9_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 154, 240, 169, 25, 100, 158, 173)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__13_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__13_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__14 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__15 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__15_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__10_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__15_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__16 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__16_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__6_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__16_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__17 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__17_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__17_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__18 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__18_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__val_quot = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_arg__val;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_str"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__2_value),LEAN_SCALAR_PTR_LITERAL(28, 110, 66, 227, 168, 59, 232, 226)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__str = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__7_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__ident___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arg_ident"};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 49, 249, 222, 84, 35, 6, 34)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__ident___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__ident = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__num___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_num"};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 247, 226, 130, 46, 200, 13, 201)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__num___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__num = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doc_arg"};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 168, 26, 226, 195, 1, 139, 142)}};
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 5, 8, 15, 213, 144, 60, 97)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "`(doc_arg| "};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 168, 26, 226, 195, 1, 139, 142)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_doc__arg_quot = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_doc__arg;
static const lean_string_object l_Lean_Doc_Syntax_anon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "anon"};
static const lean_object* l_Lean_Doc_Syntax_anon___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 30, 185, 65, 40, 8, 94, 56)}};
static const lean_object* l_Lean_Doc_Syntax_anon___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_anon___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_anon = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Anonymous positional argument "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_named___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l_Lean_Doc_Syntax_named___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_named___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 209, 4, 173, 176, 102, 100, 110)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_named___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Doc_Syntax_named___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_named___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Doc_Syntax_named___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_named___closed__9_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_named = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__10_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Named argument "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_named__no__paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "named_no_paren"};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 78, 240, 214, 103, 62, 217, 25)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__2_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_named__no__paren = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_flag__on___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flag_on"};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 222, 140, 123, 199, 224, 2, 54)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_flag__on___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_flag__on = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Boolean flag, turned on "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_flag__off___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "flag_off"};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 0, 37, 229, 12, 38, 20, 228)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_flag__off___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_flag__off = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Boolean flag, turned off "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_link__target_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "link_target"};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 92, 160, 204, 226, 167, 176, 87)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(187, 144, 133, 12, 143, 217, 129, 236)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_link__target_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "`(link_target| "};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 92, 160, 204, 226, 167, 176, 87)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_link__target_quot = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_link__target;
static const lean_string_object l_Lean_Doc_Syntax_url___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l_Lean_Doc_Syntax_url___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_url___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 109, 202, 165, 136, 148, 125, 206)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_url___closed__2_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_url___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_url = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "A URL target, written explicitly. Use square brackets for a named target. "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 197, 143, 220, 44, 158, 31, 133)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_ref___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_ref___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_ref = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "A named reference to a URL defined elsewhere. Use parentheses to write the URL here. "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_inline_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 166, 26, 13, 231, 61, 113)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(34, 76, 196, 93, 152, 249, 46, 126)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_inline_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "`(inline| "};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 166, 26, 13, 231, 61, 113)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_inline_quot = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_inline;
static const lean_string_object l_Lean_Doc_Syntax_text___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Doc_Syntax_text___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_text___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 149, 124, 218, 116, 154, 240, 105)}};
static const lean_object* l_Lean_Doc_Syntax_text___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_text___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_text = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__2_value;
static const lean_string_object l_Lean_Doc_Syntax_emph___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 183, 215, 94, 0, 242, 191, 239)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_emph___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_["};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_emph___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_emph = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 330, .m_capacity = 330, .m_length = 328, .m_data = "Emphasis, often rendered as italics.\n\nEmphasis may be nested by using longer sequences of `_` for the outer delimiters. For example:\n```\nRemember: __always butter the _rugbrød_ before adding toppings!__\n```\nHere, the outer `__` is used to emphasize the instructions, while the inner `_` indicates the use of\na non-English word.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_bold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 240, 207, 144, 35, 3, 119, 11)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_bold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "*["};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_bold = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 166, .m_capacity = 166, .m_length = 165, .m_data = "Bold emphasis.\n\nA single `*` suffices to make text bold. Using `_` for emphasis.\n\nBold text may be nested by using longer sequences of `*` for the outer delimiters.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_link___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l_Lean_Doc_Syntax_link___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_link___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 184, 35, 28, 112, 167, 76, 80)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_link___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "link["};
static const lean_object* l_Lean_Doc_Syntax_link___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_link = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "A link. The link's target may either be a concrete URL (written in parentheses) or a named URL\n(written in square brackets).\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_image___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l_Lean_Doc_Syntax_image___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_image___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 113, 65, 80, 13, 110, 129, 61)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_image___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "image("};
static const lean_object* l_Lean_Doc_Syntax_image___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_image___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_image___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_image___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_image___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_image = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 221, .m_capacity = 221, .m_length = 220, .m_data = "An image, with alternate text and a URL.\n\nThe alternate text is a plain string, rather than Verso markup.\n\nThe image URL may either be a concrete URL (written in parentheses) or a named URL (written in\nsquare brackets).\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_footnote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 87, 199, 0, 139, 133, 244, 123)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_footnote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "footnote("};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_footnote = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "A footnote use site.\n\nFootnotes must be defined elsewhere using the `[^NAME]: TEXT` syntax.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_linebreak___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 183, 85, 224, 226, 177, 67, 207)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_linebreak___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "line!"};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_linebreak = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_code___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Doc_Syntax_code___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 172, 118, 77, 213, 142, 126)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_code___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "code("};
static const lean_object* l_Lean_Doc_Syntax_code___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_code___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_code = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 448, .m_capacity = 448, .m_length = 447, .m_data = "Literal code.\n\nCode may begin with any non-zero number of backticks. It must be terminated with the same number,\nand it may not contain a sequence of backticks that is at least as long as its starting or ending\ndelimiters.\n\nIf the first and last characters are space, and it contains at least one non-space character, then\nthe resulting string has a single space stripped from each end. Thus, ``` `` `x `` ``` represents\n``\"`x\"``, not ``\" `x \"``.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_role___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l_Lean_Doc_Syntax_role___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_role___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 39, 13, 65, 153, 69, 141, 111)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_role___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "role{"};
static const lean_object* l_Lean_Doc_Syntax_role___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__6_value;
static const lean_string_object l_Lean_Doc_Syntax_role___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Doc_Syntax_role___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__6_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__9_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__10_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__11_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__12_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_role___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_role = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 762, .m_capacity = 762, .m_length = 761, .m_data = "A _role_: an extension to the Verso document language in an inline position.\n\nText is given a role using the following syntax: `{NAME ARGS*}[CONTENT]`. The `NAME` is an\nidentifier that determines which role is being used, akin to a function name. Each of the `ARGS` may\nhave the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is a sequence of inline content. If there is only one piece of content and it has\nbeginning and ending delimiters (e.g. code literals, links, or images, but not ordinary text), then\nthe `[` and `]` may be omitted. In particular, `` {NAME ARGS*}`x` `` is equivalent to\n``{NAME ARGS*}[`x`]``.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_inline__math___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 58, 152, 4, 55, 96, 114, 182)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_inline__math___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\\math"};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_inline__math = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Inline mathematical notation (equivalent to LaTeX's `$` notation) "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_display__math___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 134, 189, 58, 202, 192, 153, 244)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_display__math___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\\displaymath"};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_display__math = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Display-mode mathematical notation "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_block_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "block"};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 251, 195, 145, 15, 78, 208, 56)}};
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(209, 131, 253, 7, 152, 186, 37, 254)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_block_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "`(block| "};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 251, 195, 145, 15, 78, 208, 56)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_block_quot = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_block;
static const lean_string_object l_Lean_Doc_Syntax_list__item_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "list_item"};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 212, 251, 56, 191, 246, 167, 212)}};
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(21, 109, 214, 10, 148, 231, 82, 169)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_list__item_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "`(list_item| "};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 212, 251, 56, 191, 246, 167, 212)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_list__item_quot = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_list__item;
static const lean_string_object l_Lean_Doc_Syntax_li___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "li"};
static const lean_object* l_Lean_Doc_Syntax_li___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_li___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 229, 0, 156, 136, 247, 163, 99)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_li___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Doc_Syntax_li___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_li___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_li = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "A list item "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_desc__item_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "desc_item"};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 29, 44, 183, 55, 191, 144, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(55, 249, 160, 84, 217, 200, 245, 59)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_desc__item_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "`(desc_item| "};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 29, 44, 183, 55, 191, 144, 255)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_desc__item_quot = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_desc__item;
static const lean_string_object l_Lean_Doc_Syntax_desc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 44, 92, 80, 93, 40, 168, 47)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_desc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_desc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_desc = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "A description of an item "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_para___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l_Lean_Doc_Syntax_para___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_para___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 72, 198, 245, 142, 145, 171, 144)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_para___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "para["};
static const lean_object* l_Lean_Doc_Syntax_para___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_para___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Doc_Syntax_para___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_para___closed__4_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_para___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_para = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Paragraph "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_ul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 90, 162, 51, 92, 30, 144, 89)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_ul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ul{"};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_ul = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Unordered List "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_dl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 49, 30, 64, 139, 101, 177, 168)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_dl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dl{"};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_dl = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Description list "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_ol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 73, 192, 118, 161, 88, 51, 173)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_ol___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ol("};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_ol___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__9_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__10_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_ol = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Ordered list "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 242, 241, 127, 13, 6, 27, 177)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "```"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__8_value;
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__9_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__10_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__11_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__12_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__12_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__13_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__13_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__14 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_codeblock = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1211, .m_capacity = 1211, .m_length = 1210, .m_data = "A code block that contains literal code.\n\nCode blocks have the following syntax:\n````\n```(NAME ARGS*)\?\nCONTENT\n```\n````\n\n`CONTENT` is a literal string. If the `CONTENT` contains a sequence of three or more backticks, then\nthe opening and closing ` ``` ` (called _fences_) should have more backticks than the longest\nsequence in `CONTENT`. Additionally, the opening and closing fences should have the same number of\nbackticks.\n\nIf `NAME` and `ARGS` are not provided, then the code block represents literal text. If provided, the\n`NAME` is an identifier that selects an interpretation of the block. Unlike Markdown, this name is\nnot necessarily the language in which the code is written, though many custom code blocks are, in\npractice, named after the language that they contain. `NAME` is more akin to a function name. Each\nof the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is interpreted according to the indentation of the fences. If the fences are indented\n`n` spaces, then `n` spaces are removed from the start of each line of `CONTENT`.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_blockquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 37, 74, 205, 107, 38, 107, 223)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_blockquote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_blockquote = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "A quotation, which contains a sequence of blocks that are at least as indented as the `>`.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_link__ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "link_ref"};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 122, 52, 169, 192, 153, 29, 165)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_link__ref___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_link__ref = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "A named URL that can be used in links and images.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_footnote__ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "footnote_ref"};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 7, 163, 121, 208, 236, 208, 13)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_footnote__ref___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_footnote__ref = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A footnote definition.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_directive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 236, 126, 236, 245, 181, 4, 182)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_directive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ":::"};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_directive___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rawIdent"};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__4_value),LEAN_SCALAR_PTR_LITERAL(112, 100, 176, 236, 81, 164, 232, 12)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__10_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__9_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__11_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__12_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__12_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__13_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__13_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__14 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_directive = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 675, .m_capacity = 675, .m_length = 674, .m_data = "A _directive_, which is an extension to the Verso language in block position.\n\nDirectives have the following syntax:\n```\n:::NAME ARGS*\nCONTENT*\n:::\n```\n\nThe `NAME` is an identifier that determines which directive is being used, akin to a function name.\nEach of the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is a sequence of block content. Directives may be nested by using more colons in\nthe outer directive. For example:\n```\n::::outer +flag (arg := 5)\nA paragraph.\n:::inner \"label\"\n* 1\n* 2\n:::\n::::\n```\n\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_header___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Doc_Syntax_header___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 131, 27, 234, 140, 72, 2, 168)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_header___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "header("};
static const lean_object* l_Lean_Doc_Syntax_header___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__6_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_header___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_header = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 203, .m_capacity = 203, .m_length = 202, .m_data = "A header\n\nHeaders must be correctly nested to form a tree structure. The first header in a document must\nstart with `#`, and subsequent headers must have at most one more `#` than the preceding header.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__1;
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadataContents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__3_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__4;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__5;
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__6_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__7;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__8;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__9;
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__10_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__11;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__12;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__13;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__14;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__15;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__16;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__17;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents;
static const lean_string_object l_Lean_Doc_Syntax_metadata__block___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 201, 5, 85, 129, 97, 253, 216)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_metadata__block___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "%%%"};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_metadata__block___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "metadataContents"};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 164, 223, 160, 173, 108, 137, 29)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_metadata__block = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Metadata for the preceding header.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstField_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value)} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepByIndent_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value)} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstField_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value)} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepByIndent_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_command___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Doc_Syntax_command___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_command___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 102, 246, 27, 44, 229, 232, 70)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_command___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "command{"};
static const lean_object* l_Lean_Doc_Syntax_command___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_command___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_command___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_command___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_command___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_command = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 391, .m_capacity = 391, .m_length = 390, .m_data = "A block-level command, which invokes an extension during documentation processing.\n\nThe `NAME` is an identifier that determines which command is being used, akin to a function name.\nEach of the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_versoText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoText"};
static const lean_object* l_Lean_Doc_Parser_versoText___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoText___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 255, 240, 17, 75, 250, 253, 95)}};
static const lean_object* l_Lean_Doc_Parser_versoText___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoText___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoText___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText;
static const lean_string_object l_Lean_Doc_Parser_versoRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "versoRef"};
static const lean_object* l_Lean_Doc_Parser_versoRef___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoRef___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 44, 27, 25, 170, 146, 153, 245)}};
static const lean_object* l_Lean_Doc_Parser_versoRef___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoRef___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoRef___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoRef;
static const lean_string_object l_Lean_Doc_Parser_versoLinkUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "versoLinkUrl"};
static const lean_object* l_Lean_Doc_Parser_versoLinkUrl___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 188, 54, 130, 131, 60, 251, 148)}};
static const lean_object* l_Lean_Doc_Parser_versoLinkUrl___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoLinkUrl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoLinkUrl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkUrl;
static const lean_string_object l_Lean_Doc_Parser_versoLinkRefUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "versoLinkRefUrl"};
static const lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 57, 106, 22, 121, 78, 15, 41)}};
static const lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoLinkRefUrl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkRefUrl;
static const lean_string_object l_Lean_Doc_Parser_versoImageAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "versoImageAlt"};
static const lean_object* l_Lean_Doc_Parser_versoImageAlt___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 180, 119, 241, 128, 95, 219, 17)}};
static const lean_object* l_Lean_Doc_Parser_versoImageAlt___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoImageAlt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoImageAlt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoImageAlt;
static const lean_string_object l_Lean_Doc_Parser_versoCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoCode"};
static const lean_object* l_Lean_Doc_Parser_versoCode___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCode___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 134, 52, 97, 245, 192, 23, 73)}};
static const lean_object* l_Lean_Doc_Parser_versoCode___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoCode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoCode___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCode;
static const lean_string_object l_Lean_Doc_Parser_versoCodeBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "versoCodeBlock"};
static const lean_object* l_Lean_Doc_Parser_versoCodeBlock___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 196, 91, 225, 102, 151, 154, 53)}};
static const lean_object* l_Lean_Doc_Parser_versoCodeBlock___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoCodeBlock___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoCodeBlock___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeBlock;
static const lean_string_object l_Lean_Doc_Parser_versoCodeBlockLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "versoCodeBlockLine"};
static const lean_object* l_Lean_Doc_Parser_versoCodeBlockLine___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlockLine___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoCodeBlockLine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 10, 188, 201, 21, 143, 104, 9)}};
static const lean_object* l_Lean_Doc_Parser_versoCodeBlockLine___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoCodeBlockLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoCodeBlockLine___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeBlockLine;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoTextKind = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoRefKind = (const lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkRefUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoImageAltKind = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeKind = (const lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeBlockKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeBlockLineKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlockLine___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_longestBacktickRun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_longestBacktickRun___closed__0 = (const lean_object*)&l_Lean_Doc_longestBacktickRun___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_versoCodeBoundarySpaces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Doc_versoCodeBoundarySpaces___closed__0 = (const lean_object*)&l_Lean_Doc_versoCodeBoundarySpaces___closed__0_value;
static lean_once_cell_t l_Lean_Doc_versoCodeBoundarySpaces___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_versoCodeBoundarySpaces___closed__1;
LEAN_EXPORT uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBoundarySpaces___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_escapeVersoLinkUrl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_escapeVersoLinkUrl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_escapeVersoImageAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_escapeVersoImageAlt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
static lean_once_cell_t l_Lean_TSyntax_getVersoText___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TSyntax_getVersoText___closed__0;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLine(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLine___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCodeBlock_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCodeBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_ArgVal_str___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ArgVal.str"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__0_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_str___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ArgVal"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__4_value),LEAN_SCALAR_PTR_LITERAL(165, 66, 72, 255, 161, 123, 180, 197)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_str___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_str;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_ident___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ArgVal.ident"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__2_value),LEAN_SCALAR_PTR_LITERAL(46, 191, 138, 67, 72, 90, 15, 127)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_ident___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_ident___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_ident;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_num___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ArgVal.num"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 188, 228, 197, 246, 25, 189, 153)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_num___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_num___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_num;
static const lean_string_object l_Lean_Doc_Parser_argVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "argVal"};
static const lean_object* l_Lean_Doc_Parser_argVal___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_argVal___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_argVal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_argVal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 119, 50, 194, 18, 139, 234, 159)}};
static const lean_object* l_Lean_Doc_Parser_argVal___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_argVal___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_argVal;
static const lean_string_object l_Lean_Doc_Parser_Arg_anon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Arg"};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 126, 223, 228, 215, 141, 22, 177)}};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_anon___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_anon___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_anon;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_named___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 213, 136, 95, 26, 15, 91, 243)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__5;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__6;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__7;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 130, 4, 13, 153, 240, 131, 1)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named__no__paren;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 11, 92, 179, 92, 210, 69, 32)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__on;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 14, 2, 143, 165, 169, 65, 229)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__off;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_arg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Doc_Parser_arg___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_arg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_arg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_arg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 92, 75, 80, 50, 63, 75, 21)}};
static const lean_object* l_Lean_Doc_Parser_arg___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_arg___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_arg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_arg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_arg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_arg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___closed__5;
static lean_once_cell_t l_Lean_Doc_Parser_arg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___closed__6;
static lean_once_cell_t l_Lean_Doc_Parser_arg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___closed__7;
static lean_once_cell_t l_Lean_Doc_Parser_arg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_arg;
static const lean_string_object l_Lean_Doc_Parser_LinkTarget_url___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LinkTarget"};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_url___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 147, 211, 241, 202, 7, 251)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_url;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 54, 241, 38, 78, 206, 156, 5)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_ref;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_linkTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "linkTarget"};
static const lean_object* l_Lean_Doc_Parser_linkTarget___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 192, 153, 19, 197, 24, 81)}};
static const lean_object* l_Lean_Doc_Parser_linkTarget___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_linkTarget___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_linkTarget___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_linkTarget___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_linkTarget___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_linkTarget___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_linkTarget___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_linkTarget;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3___boxed(lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__1_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__1_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "one or more '"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "'*', '-', or '+'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawFn___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "'.' or ')'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "'0'-'9'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "a number followed by '.' or ')'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_rawFn___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit;
static const lean_string_object l_Lean_Doc_Parser_headerMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "headerMarker"};
static const lean_object* l_Lean_Doc_Parser_headerMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 163, 210, 90, 152, 248, 144, 166)}};
static const lean_object* l_Lean_Doc_Parser_headerMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_headerMarker___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_headerMarker___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_headerMarker___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_headerMarker___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_headerMarker;
static const lean_string_object l_Lean_Doc_Parser_listMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "listMarker"};
static const lean_object* l_Lean_Doc_Parser_listMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_listMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_listMarker___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 134, 18, 7, 181, 33, 85, 37)}};
static const lean_object* l_Lean_Doc_Parser_listMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_listMarker___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_listMarker___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_listMarker___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_listMarker___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_listMarker___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_listMarker___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_listMarker;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_satisfyFn___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__3_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__3_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__4_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker;
static const lean_string_object l_Lean_Doc_Parser_emphDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "emphDelimiter"};
static const lean_object* l_Lean_Doc_Parser_emphDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 57, 61, 189, 31, 180, 10, 101)}};
static const lean_object* l_Lean_Doc_Parser_emphDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_emphDelimiter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_emphDelimiter___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_emphDelimiter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_emphDelimiter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_emphDelimiter;
static const lean_string_object l_Lean_Doc_Parser_boldDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "boldDelimiter"};
static const lean_object* l_Lean_Doc_Parser_boldDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 9, 73, 54, 22, 222, 115, 214)}};
static const lean_object* l_Lean_Doc_Parser_boldDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_boldDelimiter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_boldDelimiter___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_boldDelimiter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_boldDelimiter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_boldDelimiter;
static const lean_string_object l_Lean_Doc_Parser_codeDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "codeDelimiter"};
static const lean_object* l_Lean_Doc_Parser_codeDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 116, 135, 82, 225, 37, 203, 104)}};
static const lean_object* l_Lean_Doc_Parser_codeDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_codeDelimiter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_codeDelimiter___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_codeDelimiter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_codeDelimiter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeDelimiter;
static const lean_string_object l_Lean_Doc_Parser_codeBlockFence___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "codeBlockFence"};
static const lean_object* l_Lean_Doc_Parser_codeBlockFence___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 154, 39, 84, 226, 168, 56, 199)}};
static const lean_object* l_Lean_Doc_Parser_codeBlockFence___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_codeBlockFence___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_codeBlockFence___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeBlockFence;
static const lean_string_object l_Lean_Doc_Parser_inlineMathMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inlineMathMarker"};
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 9, 108, 134, 130, 7, 90, 114)}};
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_inlineMathMarker___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_inlineMathMarker___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_inlineMathMarker___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_inlineMathMarker___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_inlineMathMarker___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_inlineMathMarker;
static const lean_string_object l_Lean_Doc_Parser_displayMathMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "displayMathMarker"};
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 18, 116, 40, 86, 165, 207, 150)}};
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_displayMathMarker___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_displayMathMarker___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_displayMathMarker___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_displayMathMarker___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_displayMathMarker___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_displayMathMarker;
static const lean_string_object l_Lean_Doc_Parser_directiveDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "directiveDelimiter"};
static const lean_object* l_Lean_Doc_Parser_directiveDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 28, 38, 38, 72, 11, 173, 25)}};
static const lean_object* l_Lean_Doc_Parser_directiveDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_directiveDelimiter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_directiveDelimiter___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_directiveDelimiter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_directiveDelimiter___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_directiveDelimiter;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "' to close what '"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "' opened"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Inline"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 30, 73, 79, 76, 254, 8, 196)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 150, 35, 119, 78, 160, 253, 84)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_image___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 170, 102, 209, 119, 14, 254, 233)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 121, 147, 210, 143, 103, 0, 217)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 236, 9, 179, 133, 206, 252, 7)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 39, 73, 53, 10, 24, 181, 77)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_text___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 133, 107, 199, 31, 216, 160, 200)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 21, 54, 220, 135, 144, 211, 134)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 215, 18, 85, 144, 91, 153, 50)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_link___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 237, 8, 103, 58, 149, 183, 251)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 108, 76, 164, 130, 208, 234, 146)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_role___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 233, 178, 241, 96, 238, 218, 92)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_text___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_text___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_text;
static const lean_closure_object l_Lean_Doc_Parser_Inline_emph___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_emph___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_emph___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_emph___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_emph = (const lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Inline_bold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_bold___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_bold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_bold___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_bold = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_code;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_inline__math;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_display__math;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Inline_link___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_link___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_link___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_link___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_link = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_image___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_image___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_image;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_footnote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_footnote___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_footnote;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_linebreak___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_linebreak___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_linebreak;
static const lean_closure_object l_Lean_Doc_Parser_Inline_role___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_role___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_role___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_role___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_role = (const lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_inline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_inline___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_inline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_inline___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_inline = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Block"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_para___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 167, 213, 66, 92, 160, 222, 146)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_command___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 232, 253, 29, 141, 75, 139, 21)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 125, 116, 48, 167, 45, 110, 42)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 233, 128, 119, 237, 18, 215)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 53, 29, 246, 154, 171, 121, 154)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 176, 128, 73, 36, 235, 244, 141)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 32, 43, 99, 217, 167, 97, 87)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 15, 76, 66, 114, 120, 124, 74)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DescItem.item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DescItem"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 70, 30, 3, 105, 156, 130, 115)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 193, 144, 210, 183, 212, 114, 89)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 45, 1, 212, 241, 159, 201, 84)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ListItem.item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ListItem"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(154, 153, 101, 209, 126, 16, 11, 208)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 123, 16, 134, 76, 179, 171, 228)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 199, 227, 191, 40, 60, 185, 243)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 145, 178, 243, 42, 6, 105, 104)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 234, 1, 42, 159, 198, 19, 176)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 72, 202, 40, 103, 170, 246, 9)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_ListItem_item___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ListItem_item___closed__0;
static lean_once_cell_t l_Lean_Doc_Parser_ListItem_item___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ListItem_item___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ListItem_item;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_DescItem_item___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_DescItem_item___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_DescItem_item___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_DescItem_item___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_DescItem_item = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_para___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_para___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_para;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_ul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_ul___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_ul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_ul___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_ul = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_ol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_ol___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_ol___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_ol___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_ol = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_dl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_dl___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_dl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_dl___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_dl = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_blockquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_blockquote___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_blockquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_blockquote___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_blockquote = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_codeblock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_codeblock___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_codeblock;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_directive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_directive___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_directive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_directive___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_directive = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_header___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_header___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_header;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_link__ref___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_link__ref___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_link__ref;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_footnote__ref___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_footnote__ref;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_metadata__block___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_metadata__block___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_metadata__block;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_command___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_command___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_command;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_block___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_block___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_block___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_block___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_block___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_block___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_block___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_block = (const lean_object*)&l_Lean_Doc_Parser_block___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_document___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "document"};
static const lean_object* l_Lean_Doc_Parser_document___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_document___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_document___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_document___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 113, 152, 229, 184, 253, 250, 127)}};
static const lean_object* l_Lean_Doc_Parser_document___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_document___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_document___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_document___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_document___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_document___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_document___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_document___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_getVersoBlocks___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__3 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__4 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__5 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__6 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__7 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__8 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__9 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__10 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__11 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__12 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__13 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__14 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__15 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__16 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__17 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__18 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__19 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__20 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__21 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__22 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
static lean_object* _init_l_Lean_Parser_Category_arg__val(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Parser_Category_doc__arg(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1(){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((lean_object*)(l_Lean_Doc_Syntax_anon___closed__1));
v___x_140_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0));
v___x_141_ = l_Lean_addBuiltinDocString(v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1(){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__1));
v___x_180_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_181_ = l_Lean_addBuiltinDocString(v___x_179_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___boxed(lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1(){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l_Lean_Doc_Syntax_named__no__paren___closed__1));
v___x_205_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_206_ = l_Lean_addBuiltinDocString(v___x_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1___boxed(lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1(){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__1));
v___x_230_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0));
v___x_231_ = l_Lean_addBuiltinDocString(v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___boxed(lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1(){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__1));
v___x_255_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0));
v___x_256_ = l_Lean_addBuiltinDocString(v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___boxed(lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
return v_res_258_;
}
}
static lean_object* _init_l_Lean_Parser_Category_link__target(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1(){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((lean_object*)(l_Lean_Doc_Syntax_url___closed__1));
v___x_311_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0));
v___x_312_ = l_Lean_addBuiltinDocString(v___x_310_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___boxed(lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1(){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__1));
v___x_343_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0));
v___x_344_ = l_Lean_addBuiltinDocString(v___x_342_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___boxed(lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
return v_res_346_;
}
}
static lean_object* _init_l_Lean_Parser_Category_inline(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1(){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = ((lean_object*)(l_Lean_Doc_Syntax_emph___closed__1));
v___x_419_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0));
v___x_420_ = l_Lean_addBuiltinDocString(v___x_418_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___boxed(lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1(){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((lean_object*)(l_Lean_Doc_Syntax_bold___closed__1));
v___x_448_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0));
v___x_449_ = l_Lean_addBuiltinDocString(v___x_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___boxed(lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1(){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((lean_object*)(l_Lean_Doc_Syntax_link___closed__1));
v___x_481_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0));
v___x_482_ = l_Lean_addBuiltinDocString(v___x_480_, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___boxed(lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1(){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = ((lean_object*)(l_Lean_Doc_Syntax_image___closed__1));
v___x_514_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0));
v___x_515_ = l_Lean_addBuiltinDocString(v___x_513_, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___boxed(lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1(){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote___closed__1));
v___x_543_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0));
v___x_544_ = l_Lean_addBuiltinDocString(v___x_542_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___boxed(lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1(){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((lean_object*)(l_Lean_Doc_Syntax_code___closed__1));
v___x_590_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0));
v___x_591_ = l_Lean_addBuiltinDocString(v___x_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___boxed(lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1(){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__1));
v___x_641_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0));
v___x_642_ = l_Lean_addBuiltinDocString(v___x_640_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___boxed(lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1(){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l_Lean_Doc_Syntax_inline__math___closed__1));
v___x_666_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0));
v___x_667_ = l_Lean_addBuiltinDocString(v___x_665_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___boxed(lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1(){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l_Lean_Doc_Syntax_display__math___closed__1));
v___x_691_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0));
v___x_692_ = l_Lean_addBuiltinDocString(v___x_690_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___boxed(lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
return v_res_694_;
}
}
static lean_object* _init_l_Lean_Parser_Category_block(void){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_box(0);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Parser_Category_list__item(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = lean_box(0);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1(){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((lean_object*)(l_Lean_Doc_Syntax_li___closed__1));
v___x_779_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0));
v___x_780_ = l_Lean_addBuiltinDocString(v___x_778_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___boxed(lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
return v_res_782_;
}
}
static lean_object* _init_l_Lean_Parser_Category_desc__item(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_box(0);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1(){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l_Lean_Doc_Syntax_desc___closed__1));
v___x_845_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0));
v___x_846_ = l_Lean_addBuiltinDocString(v___x_844_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___boxed(lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1(){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l_Lean_Doc_Syntax_para___closed__1));
v___x_880_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0));
v___x_881_ = l_Lean_addBuiltinDocString(v___x_879_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___boxed(lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1(){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((lean_object*)(l_Lean_Doc_Syntax_ul___closed__1));
v___x_912_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0));
v___x_913_ = l_Lean_addBuiltinDocString(v___x_911_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___boxed(lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1(){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l_Lean_Doc_Syntax_dl___closed__1));
v___x_944_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0));
v___x_945_ = l_Lean_addBuiltinDocString(v___x_943_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___boxed(lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1(){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__1));
v___x_988_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0));
v___x_989_ = l_Lean_addBuiltinDocString(v___x_987_, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___boxed(lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1(){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((lean_object*)(l_Lean_Doc_Syntax_codeblock___closed__1));
v___x_1038_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0));
v___x_1039_ = l_Lean_addBuiltinDocString(v___x_1037_, v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___boxed(lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1(){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__1));
v___x_1063_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0));
v___x_1064_ = l_Lean_addBuiltinDocString(v___x_1062_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___boxed(lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1(){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__1));
v___x_1092_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0));
v___x_1093_ = l_Lean_addBuiltinDocString(v___x_1091_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___boxed(lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1(){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__1));
v___x_1125_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0));
v___x_1126_ = l_Lean_addBuiltinDocString(v___x_1124_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___boxed(lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1(){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = ((lean_object*)(l_Lean_Doc_Syntax_directive___closed__1));
v___x_1177_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0));
v___x_1178_ = l_Lean_addBuiltinDocString(v___x_1176_, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___boxed(lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1(){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = ((lean_object*)(l_Lean_Doc_Syntax_header___closed__1));
v___x_1218_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0));
v___x_1219_ = l_Lean_addBuiltinDocString(v___x_1217_, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___boxed(lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
return v_res_1221_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__0));
v___x_1224_ = l_Lean_Parser_symbol(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__4(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Doc_Syntax_li___closed__2));
v___x_1229_ = l_Lean_Parser_symbol(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__5(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_p_1233_; 
v___x_1230_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__4, &l_Lean_Doc_Syntax_metadataContents___closed__4_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__4);
v___x_1231_ = l_Lean_Parser_Term_structInstField;
v___x_1232_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__3));
v_p_1233_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1232_, v___x_1231_, v___x_1230_);
return v_p_1233_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__7(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__6));
v___x_1236_ = l_Lean_Parser_checkColGe(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__8(void){
_start:
{
lean_object* v_p_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_p_1237_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__5, &l_Lean_Doc_Syntax_metadataContents___closed__5_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__5);
v___x_1238_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__7, &l_Lean_Doc_Syntax_metadataContents___closed__7_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__7);
v___x_1239_ = l_Lean_Parser_andthen(v___x_1238_, v_p_1237_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__9(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__6));
v___x_1241_ = l_Lean_Parser_checkColEq(v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__11(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__10));
v___x_1244_ = l_Lean_Parser_checkLinebreakBefore(v___x_1243_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__12(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = l_Lean_Parser_pushNone;
v___x_1246_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__11, &l_Lean_Doc_Syntax_metadataContents___closed__11_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__11);
v___x_1247_ = l_Lean_Parser_andthen(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__13(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__12, &l_Lean_Doc_Syntax_metadataContents___closed__12_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__12);
v___x_1249_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__9, &l_Lean_Doc_Syntax_metadataContents___closed__9_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__9);
v___x_1250_ = l_Lean_Parser_andthen(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__14(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__13, &l_Lean_Doc_Syntax_metadataContents___closed__13_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__13);
v___x_1252_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__1, &l_Lean_Doc_Syntax_metadataContents___closed__1_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__1);
v___x_1253_ = l_Lean_Parser_orelse(v___x_1252_, v___x_1251_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__15(void){
_start:
{
uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1254_ = 1;
v___x_1255_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__14, &l_Lean_Doc_Syntax_metadataContents___closed__14_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__14);
v___x_1256_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__0));
v___x_1257_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__8, &l_Lean_Doc_Syntax_metadataContents___closed__8_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__8);
v___x_1258_ = l_Lean_Parser_sepBy(v___x_1257_, v___x_1256_, v___x_1255_, v___x_1254_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__16(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__15, &l_Lean_Doc_Syntax_metadataContents___closed__15_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__15);
v___x_1260_ = l_Lean_Parser_withPosition(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__17(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__16, &l_Lean_Doc_Syntax_metadataContents___closed__16_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__16);
v___x_1262_ = l_Lean_Parser_Term_structInstFields(v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents(void){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__17, &l_Lean_Doc_Syntax_metadataContents___closed__17_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__17);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1(){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__1));
v___x_1297_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0));
v___x_1298_ = l_Lean_addBuiltinDocString(v___x_1296_, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___boxed(lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter(lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents_formatter___closed__2));
v___x_1314_ = l_Lean_Parser_Term_structInstFields_formatter(v___x_1313_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___boxed(lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Doc_Syntax_metadataContents_formatter(v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer(lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2));
v___x_1336_ = l_Lean_Parser_Term_structInstFields_parenthesizer(v___x_1335_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___boxed(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Doc_Syntax_metadataContents_parenthesizer(v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1(){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = ((lean_object*)(l_Lean_Doc_Syntax_command___closed__1));
v___x_1372_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0));
v___x_1373_ = l_Lean_addBuiltinDocString(v___x_1371_, v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___boxed(lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
return v_res_1375_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoText___closed__2(void){
_start:
{
uint8_t v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1382_ = 0;
v___x_1383_ = 1;
v___x_1384_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__1));
v___x_1385_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__0));
v___x_1386_ = l_Lean_Parser_mkAntiquot(v___x_1385_, v___x_1384_, v___x_1383_, v___x_1382_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoText(void){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_obj_once(&l_Lean_Doc_Parser_versoText___closed__2, &l_Lean_Doc_Parser_versoText___closed__2_once, _init_l_Lean_Doc_Parser_versoText___closed__2);
return v___x_1387_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoRef___closed__2(void){
_start:
{
uint8_t v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1394_ = 0;
v___x_1395_ = 1;
v___x_1396_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef___closed__1));
v___x_1397_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef___closed__0));
v___x_1398_ = l_Lean_Parser_mkAntiquot(v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoRef(void){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_obj_once(&l_Lean_Doc_Parser_versoRef___closed__2, &l_Lean_Doc_Parser_versoRef___closed__2_once, _init_l_Lean_Doc_Parser_versoRef___closed__2);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkUrl___closed__2(void){
_start:
{
uint8_t v___x_1406_; uint8_t v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1406_ = 0;
v___x_1407_ = 1;
v___x_1408_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl___closed__1));
v___x_1409_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl___closed__0));
v___x_1410_ = l_Lean_Parser_mkAntiquot(v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_);
return v___x_1410_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkUrl(void){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = lean_obj_once(&l_Lean_Doc_Parser_versoLinkUrl___closed__2, &l_Lean_Doc_Parser_versoLinkUrl___closed__2_once, _init_l_Lean_Doc_Parser_versoLinkUrl___closed__2);
return v___x_1411_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkRefUrl___closed__2(void){
_start:
{
uint8_t v___x_1418_; uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1418_ = 0;
v___x_1419_ = 1;
v___x_1420_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl___closed__1));
v___x_1421_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl___closed__0));
v___x_1422_ = l_Lean_Parser_mkAntiquot(v___x_1421_, v___x_1420_, v___x_1419_, v___x_1418_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkRefUrl(void){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_obj_once(&l_Lean_Doc_Parser_versoLinkRefUrl___closed__2, &l_Lean_Doc_Parser_versoLinkRefUrl___closed__2_once, _init_l_Lean_Doc_Parser_versoLinkRefUrl___closed__2);
return v___x_1423_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoImageAlt___closed__2(void){
_start:
{
uint8_t v___x_1430_; uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1430_ = 0;
v___x_1431_ = 1;
v___x_1432_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt___closed__1));
v___x_1433_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt___closed__0));
v___x_1434_ = l_Lean_Parser_mkAntiquot(v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_);
return v___x_1434_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoImageAlt(void){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_obj_once(&l_Lean_Doc_Parser_versoImageAlt___closed__2, &l_Lean_Doc_Parser_versoImageAlt___closed__2_once, _init_l_Lean_Doc_Parser_versoImageAlt___closed__2);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCode___closed__2(void){
_start:
{
uint8_t v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1442_ = 0;
v___x_1443_ = 1;
v___x_1444_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode___closed__1));
v___x_1445_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode___closed__0));
v___x_1446_ = l_Lean_Parser_mkAntiquot(v___x_1445_, v___x_1444_, v___x_1443_, v___x_1442_);
return v___x_1446_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCode(void){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_obj_once(&l_Lean_Doc_Parser_versoCode___closed__2, &l_Lean_Doc_Parser_versoCode___closed__2_once, _init_l_Lean_Doc_Parser_versoCode___closed__2);
return v___x_1447_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlock___closed__2(void){
_start:
{
uint8_t v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1454_ = 0;
v___x_1455_ = 1;
v___x_1456_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___closed__1));
v___x_1457_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___closed__0));
v___x_1458_ = l_Lean_Parser_mkAntiquot(v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlock(void){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeBlock___closed__2, &l_Lean_Doc_Parser_versoCodeBlock___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeBlock___closed__2);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlockLine___closed__2(void){
_start:
{
uint8_t v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = 0;
v___x_1467_ = 1;
v___x_1468_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlockLine___closed__1));
v___x_1469_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlockLine___closed__0));
v___x_1470_ = l_Lean_Parser_mkAntiquot(v___x_1469_, v___x_1468_, v___x_1467_, v___x_1466_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlockLine(void){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeBlockLine___closed__2, &l_Lean_Doc_Parser_versoCodeBlockLine___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeBlockLine___closed__2);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v___x_1480_, lean_object* v_str_1481_, lean_object* v_a_1482_, lean_object* v_b_1483_){
_start:
{
uint8_t v_decide_1484_; 
v_decide_1484_ = lean_nat_dec_eq(v_a_1482_, v___x_1480_);
if (v_decide_1484_ == 0)
{
lean_object* v_fst_1485_; lean_object* v_snd_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1510_; 
v_fst_1485_ = lean_ctor_get(v_b_1483_, 0);
v_snd_1486_ = lean_ctor_get(v_b_1483_, 1);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_b_1483_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1488_ = v_b_1483_;
v_isShared_1489_ = v_isSharedCheck_1510_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snd_1486_);
lean_inc(v_fst_1485_);
lean_dec(v_b_1483_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1510_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint32_t v___x_1490_; lean_object* v___x_1491_; uint32_t v___x_1492_; uint8_t v___x_1493_; 
v___x_1490_ = lean_string_utf8_get_fast(v_str_1481_, v_a_1482_);
v___x_1491_ = lean_string_utf8_next_fast(v_str_1481_, v_a_1482_);
lean_dec(v_a_1482_);
v___x_1492_ = 96;
v___x_1493_ = lean_uint32_dec_eq(v___x_1490_, v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v_best_1494_; lean_object* v___x_1496_; 
lean_dec(v_snd_1486_);
v_best_1494_ = lean_unsigned_to_nat(0u);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v_best_1494_);
v___x_1496_ = v___x_1488_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_fst_1485_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_best_1494_);
v___x_1496_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
v_a_1482_ = v___x_1491_;
v_b_1483_ = v___x_1496_;
goto _start;
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_snd_1486_, v___x_1499_);
lean_dec(v_snd_1486_);
v___x_1501_ = lean_nat_dec_lt(v_fst_1485_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1503_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v___x_1500_);
v___x_1503_ = v___x_1488_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_fst_1485_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1500_);
v___x_1503_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
v_a_1482_ = v___x_1491_;
v_b_1483_ = v___x_1503_;
goto _start;
}
}
else
{
lean_object* v___x_1507_; 
lean_dec(v_fst_1485_);
lean_inc(v___x_1500_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v___x_1500_);
lean_ctor_set(v___x_1488_, 0, v___x_1500_);
v___x_1507_ = v___x_1488_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1500_);
v___x_1507_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
v_a_1482_ = v___x_1491_;
v_b_1483_ = v___x_1507_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_1482_);
return v_b_1483_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v___x_1511_, lean_object* v_str_1512_, lean_object* v_a_1513_, lean_object* v_b_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1511_, v_str_1512_, v_a_1513_, v_b_1514_);
lean_dec_ref(v_str_1512_);
lean_dec(v___x_1511_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun(lean_object* v_str_1518_){
_start:
{
lean_object* v_best_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_fst_1525_; 
v_best_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = ((lean_object*)(l_Lean_Doc_longestBacktickRun___closed__0));
v___x_1521_ = lean_string_utf8_byte_size(v_str_1518_);
lean_inc_ref(v_str_1518_);
v___x_1522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1522_, 0, v_str_1518_);
lean_ctor_set(v___x_1522_, 1, v_best_1519_);
lean_ctor_set(v___x_1522_, 2, v___x_1521_);
v___x_1523_ = l_String_Slice_positions(v___x_1522_);
lean_dec_ref_known(v___x_1522_, 3);
v___x_1524_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1521_, v_str_1518_, v___x_1523_, v___x_1520_);
lean_dec_ref(v_str_1518_);
v_fst_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_fst_1525_);
lean_dec_ref(v___x_1524_);
return v_fst_1525_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v_str_1528_, lean_object* v_inst_1529_, lean_object* v_R_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_, lean_object* v_c_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1527_, v_str_1528_, v_a_1531_, v_b_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v___x_1535_, lean_object* v___x_1536_, lean_object* v_str_1537_, lean_object* v_inst_1538_, lean_object* v_R_1539_, lean_object* v_a_1540_, lean_object* v_b_1541_, lean_object* v_c_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(v___x_1535_, v___x_1536_, v_str_1537_, v_inst_1538_, v_R_1539_, v_a_1540_, v_b_1541_, v_c_1542_);
lean_dec_ref(v_str_1537_);
lean_dec(v___x_1536_);
lean_dec_ref(v___x_1535_);
return v_res_1543_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(lean_object* v_s_1544_, uint8_t v___x_1545_, lean_object* v_a_1546_, uint8_t v_b_1547_){
_start:
{
lean_object* v_str_1548_; lean_object* v_startInclusive_1549_; lean_object* v_endExclusive_1550_; lean_object* v___x_1551_; uint8_t v_decide_1552_; 
v_str_1548_ = lean_ctor_get(v_s_1544_, 0);
v_startInclusive_1549_ = lean_ctor_get(v_s_1544_, 1);
v_endExclusive_1550_ = lean_ctor_get(v_s_1544_, 2);
v___x_1551_ = lean_nat_sub(v_endExclusive_1550_, v_startInclusive_1549_);
v_decide_1552_ = lean_nat_dec_eq(v_a_1546_, v___x_1551_);
lean_dec(v___x_1551_);
if (v_decide_1552_ == 0)
{
lean_object* v___x_1553_; uint32_t v___x_1558_; uint32_t v___x_1559_; uint8_t v___x_1560_; 
v___x_1553_ = lean_nat_add(v_startInclusive_1549_, v_a_1546_);
lean_dec(v_a_1546_);
v___x_1558_ = lean_string_utf8_get_fast(v_str_1548_, v___x_1553_);
v___x_1559_ = 32;
v___x_1560_ = lean_uint32_dec_eq(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
if (v___x_1545_ == 0)
{
goto v___jp_1554_;
}
else
{
lean_dec(v___x_1553_);
return v___x_1545_;
}
}
else
{
goto v___jp_1554_;
}
v___jp_1554_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_string_utf8_next_fast(v_str_1548_, v___x_1553_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_nat_sub(v___x_1555_, v_startInclusive_1549_);
v_a_1546_ = v___x_1556_;
v_b_1547_ = v_decide_1552_;
goto _start;
}
}
else
{
lean_dec(v_a_1546_);
return v_b_1547_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg___boxed(lean_object* v_s_1561_, lean_object* v___x_1562_, lean_object* v_a_1563_, lean_object* v_b_1564_){
_start:
{
uint8_t v___x_965__boxed_1565_; uint8_t v_b_boxed_1566_; uint8_t v_res_1567_; lean_object* v_r_1568_; 
v___x_965__boxed_1565_ = lean_unbox(v___x_1562_);
v_b_boxed_1566_ = lean_unbox(v_b_1564_);
v_res_1567_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1561_, v___x_965__boxed_1565_, v_a_1563_, v_b_boxed_1566_);
lean_dec_ref(v_s_1561_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(uint8_t v___x_1569_, lean_object* v_s_1570_){
_start:
{
lean_object* v_searcher_1571_; uint8_t v___x_1572_; uint8_t v___x_1573_; 
v_searcher_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = 0;
v___x_1573_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1570_, v___x_1569_, v_searcher_1571_, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0___boxed(lean_object* v___x_1574_, lean_object* v_s_1575_){
_start:
{
uint8_t v___x_988__boxed_1576_; uint8_t v_res_1577_; lean_object* v_r_1578_; 
v___x_988__boxed_1576_ = lean_unbox(v___x_1574_);
v_res_1577_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_988__boxed_1576_, v_s_1575_);
lean_dec_ref(v_s_1575_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
static lean_object* _init_l_Lean_Doc_versoCodeBoundarySpaces___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_1581_ = lean_string_utf8_byte_size(v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object* v_str_1582_){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1583_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_1584_ = lean_string_utf8_byte_size(v_str_1582_);
v___x_1585_ = lean_obj_once(&l_Lean_Doc_versoCodeBoundarySpaces___closed__1, &l_Lean_Doc_versoCodeBoundarySpaces___closed__1_once, _init_l_Lean_Doc_versoCodeBoundarySpaces___closed__1);
v___x_1586_ = lean_nat_dec_le(v___x_1585_, v___x_1584_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v_str_1582_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = lean_unsigned_to_nat(0u);
v___x_1588_ = lean_string_memcmp(v_str_1582_, v___x_1583_, v___x_1587_, v___x_1587_, v___x_1585_);
if (v___x_1588_ == 0)
{
lean_dec_ref(v_str_1582_);
return v___x_1588_;
}
else
{
if (v___x_1586_ == 0)
{
lean_dec_ref(v_str_1582_);
return v___x_1586_;
}
else
{
lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = lean_nat_sub(v___x_1584_, v___x_1585_);
v___x_1590_ = lean_string_memcmp(v_str_1582_, v___x_1583_, v___x_1589_, v___x_1587_, v___x_1585_);
lean_dec(v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec_ref(v_str_1582_);
return v___x_1590_;
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1591_, 0, v_str_1582_);
lean_ctor_set(v___x_1591_, 1, v___x_1587_);
lean_ctor_set(v___x_1591_, 2, v___x_1584_);
v___x_1592_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_1590_, v___x_1591_);
lean_dec_ref_known(v___x_1591_, 3);
return v___x_1592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBoundarySpaces___boxed(lean_object* v_str_1593_){
_start:
{
uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_res_1594_ = l_Lean_Doc_versoCodeBoundarySpaces(v_str_1593_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(lean_object* v_s_1596_, uint8_t v___x_1597_, lean_object* v_inst_1598_, lean_object* v_R_1599_, lean_object* v_a_1600_, uint8_t v_b_1601_, lean_object* v_c_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1596_, v___x_1597_, v_a_1600_, v_b_1601_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___boxed(lean_object* v_s_1604_, lean_object* v___x_1605_, lean_object* v_inst_1606_, lean_object* v_R_1607_, lean_object* v_a_1608_, lean_object* v_b_1609_, lean_object* v_c_1610_){
_start:
{
uint8_t v___x_1024__boxed_1611_; uint8_t v_b_boxed_1612_; uint8_t v_res_1613_; lean_object* v_r_1614_; 
v___x_1024__boxed_1611_ = lean_unbox(v___x_1605_);
v_b_boxed_1612_ = lean_unbox(v_b_1609_);
v_res_1613_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(v_s_1604_, v___x_1024__boxed_1611_, v_inst_1606_, v_R_1607_, v_a_1608_, v_b_boxed_1612_, v_c_1610_);
lean_dec_ref(v_s_1604_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(lean_object* v_str_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1645_; 
v_fst_1617_ = lean_ctor_get(v_a_1616_, 0);
v_snd_1618_ = lean_ctor_get(v_a_1616_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_a_1616_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1620_ = v_a_1616_;
v_isShared_1621_ = v_isSharedCheck_1645_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_snd_1618_);
lean_inc(v_fst_1617_);
lean_dec(v_a_1616_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1645_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; uint8_t v_decide_1623_; 
v___x_1622_ = lean_string_utf8_byte_size(v_str_1615_);
v_decide_1623_ = lean_nat_dec_eq(v_snd_1618_, v___x_1622_);
if (v_decide_1623_ == 0)
{
uint32_t v___x_1624_; lean_object* v___x_1625_; uint32_t v___x_1631_; uint8_t v___x_1632_; 
v___x_1624_ = lean_string_utf8_get_fast(v_str_1615_, v_snd_1618_);
v___x_1625_ = lean_string_utf8_next_fast(v_str_1615_, v_snd_1618_);
lean_dec(v_snd_1618_);
v___x_1631_ = 92;
v___x_1632_ = lean_uint32_dec_eq(v___x_1624_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_del_object(v___x_1620_);
v___x_1633_ = lean_string_push(v_fst_1617_, v___x_1624_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v___x_1625_);
v_a_1616_ = v___x_1634_;
goto _start;
}
else
{
uint8_t v_decide_1636_; 
v_decide_1636_ = lean_nat_dec_eq(v___x_1625_, v___x_1622_);
if (v_decide_1636_ == 0)
{
if (v___x_1632_ == 0)
{
goto v___jp_1626_;
}
else
{
uint32_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_del_object(v___x_1620_);
v___x_1637_ = lean_string_utf8_get_fast(v_str_1615_, v___x_1625_);
v___x_1638_ = lean_string_push(v_fst_1617_, v___x_1637_);
v___x_1639_ = lean_string_utf8_next_fast(v_str_1615_, v___x_1625_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v_a_1616_ = v___x_1640_;
goto _start;
}
}
else
{
goto v___jp_1626_;
}
}
v___jp_1626_:
{
lean_object* v___x_1628_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___x_1625_);
v___x_1628_ = v___x_1620_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___x_1625_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
v_a_1616_ = v___x_1628_;
goto _start;
}
}
}
else
{
lean_object* v___x_1643_; 
if (v_isShared_1621_ == 0)
{
v___x_1643_ = v___x_1620_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_fst_1617_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_snd_1618_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg___boxed(lean_object* v_str_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1646_, v_a_1647_);
lean_dec_ref(v_str_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(lean_object* v_str_1653_){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_fst_1656_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1));
v___x_1655_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1653_, v___x_1654_);
v_fst_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_fst_1656_);
lean_dec_ref(v___x_1655_);
return v_fst_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___boxed(lean_object* v_str_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_str_1657_);
lean_dec_ref(v_str_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(lean_object* v_str_1659_, lean_object* v_inst_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1659_, v_a_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___boxed(lean_object* v_str_1663_, lean_object* v_inst_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(v_str_1663_, v_inst_1664_, v_a_1665_);
lean_dec_ref(v_str_1663_);
return v_res_1666_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(uint32_t v_a_1667_, lean_object* v_x_1668_){
_start:
{
if (lean_obj_tag(v_x_1668_) == 0)
{
uint8_t v___x_1669_; 
v___x_1669_ = 0;
return v___x_1669_;
}
else
{
lean_object* v_head_1670_; lean_object* v_tail_1671_; uint32_t v___x_1672_; uint8_t v___x_1673_; 
v_head_1670_ = lean_ctor_get(v_x_1668_, 0);
v_tail_1671_ = lean_ctor_get(v_x_1668_, 1);
v___x_1672_ = lean_unbox_uint32(v_head_1670_);
v___x_1673_ = lean_uint32_dec_eq(v_a_1667_, v___x_1672_);
if (v___x_1673_ == 0)
{
v_x_1668_ = v_tail_1671_;
goto _start;
}
else
{
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0___boxed(lean_object* v_a_1675_, lean_object* v_x_1676_){
_start:
{
uint32_t v_a_boxed_1677_; uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_a_boxed_1677_ = lean_unbox_uint32(v_a_1675_);
lean_dec(v_a_1675_);
v_res_1678_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v_a_boxed_1677_, v_x_1676_);
lean_dec(v_x_1676_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(lean_object* v_delimiters_1680_, lean_object* v___x_1681_, lean_object* v_value_1682_, lean_object* v_a_1683_, lean_object* v_b_1684_){
_start:
{
uint8_t v_decide_1685_; 
v_decide_1685_ = lean_nat_dec_eq(v_a_1683_, v___x_1681_);
if (v_decide_1685_ == 0)
{
uint32_t v___x_1686_; lean_object* v___x_1687_; uint32_t v___x_1688_; uint8_t v___x_1693_; 
v___x_1686_ = lean_string_utf8_get_fast(v_value_1682_, v_a_1683_);
v___x_1687_ = lean_string_utf8_next_fast(v_value_1682_, v_a_1683_);
lean_dec(v_a_1683_);
v___x_1688_ = 92;
v___x_1693_ = lean_uint32_dec_eq(v___x_1686_, v___x_1688_);
if (v___x_1693_ == 0)
{
uint8_t v___x_1694_; 
v___x_1694_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v___x_1686_, v_delimiters_1680_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_string_push(v_b_1684_, v___x_1686_);
v_a_1683_ = v___x_1687_;
v_b_1684_ = v___x_1695_;
goto _start;
}
else
{
goto v___jp_1689_;
}
}
else
{
goto v___jp_1689_;
}
v___jp_1689_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_string_push(v_b_1684_, v___x_1688_);
v___x_1691_ = lean_string_push(v___x_1690_, v___x_1686_);
v_a_1683_ = v___x_1687_;
v_b_1684_ = v___x_1691_;
goto _start;
}
}
else
{
lean_dec(v_a_1683_);
return v_b_1684_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg___boxed(lean_object* v_delimiters_1697_, lean_object* v___x_1698_, lean_object* v_value_1699_, lean_object* v_a_1700_, lean_object* v_b_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1697_, v___x_1698_, v_value_1699_, v_a_1700_, v_b_1701_);
lean_dec_ref(v_value_1699_);
lean_dec(v___x_1698_);
lean_dec(v_delimiters_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(lean_object* v_delimiters_1703_, lean_object* v_value_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1705_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = lean_string_utf8_byte_size(v_value_1704_);
lean_inc_ref(v_value_1704_);
v___x_1708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1708_, 0, v_value_1704_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
lean_ctor_set(v___x_1708_, 2, v___x_1707_);
v___x_1709_ = l_String_Slice_positions(v___x_1708_);
lean_dec_ref_known(v___x_1708_, 3);
v___x_1710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1703_, v___x_1707_, v_value_1704_, v___x_1709_, v___x_1705_);
lean_dec_ref(v_value_1704_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited___boxed(lean_object* v_delimiters_1711_, lean_object* v_value_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v_delimiters_1711_, v_value_1712_);
lean_dec(v_delimiters_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(lean_object* v_delimiters_1714_, lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v_value_1717_, lean_object* v_inst_1718_, lean_object* v_R_1719_, lean_object* v_a_1720_, lean_object* v_b_1721_, lean_object* v_c_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1714_, v___x_1716_, v_value_1717_, v_a_1720_, v_b_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___boxed(lean_object* v_delimiters_1724_, lean_object* v___x_1725_, lean_object* v___x_1726_, lean_object* v_value_1727_, lean_object* v_inst_1728_, lean_object* v_R_1729_, lean_object* v_a_1730_, lean_object* v_b_1731_, lean_object* v_c_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(v_delimiters_1724_, v___x_1725_, v___x_1726_, v_value_1727_, v_inst_1728_, v_R_1729_, v_a_1730_, v_b_1731_, v_c_1732_);
lean_dec_ref(v_value_1727_);
lean_dec(v___x_1726_);
lean_dec_ref(v___x_1725_);
lean_dec(v_delimiters_1724_);
return v_res_1733_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = 41;
v___x_1735_ = lean_box_uint32(v___x_1734_);
return v___x_1735_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_box(0);
v___x_1737_ = l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1;
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___x_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object* v_value_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_obj_once(&l_Lean_Doc_escapeVersoLinkUrl___closed__0, &l_Lean_Doc_escapeVersoLinkUrl___closed__0_once, _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0);
v___x_1741_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_1740_, v_value_1739_);
return v___x_1741_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = 93;
v___x_1743_ = lean_box_uint32(v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_box(0);
v___x_1745_ = l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
v___x_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
lean_ctor_set(v___x_1746_, 1, v___x_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object* v_value_1747_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_obj_once(&l_Lean_Doc_escapeVersoImageAlt___closed__0, &l_Lean_Doc_escapeVersoImageAlt___closed__0_once, _init_l_Lean_Doc_escapeVersoImageAlt___closed__0);
v___x_1749_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_1748_, v_value_1747_);
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_TSyntax_getVersoText___closed__0(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1751_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText(lean_object* v_s_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_1754_ = l_Lean_Syntax_isLit_x3f(v___x_1753_, v_s_1752_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1755_;
}
else
{
lean_object* v_val_1756_; lean_object* v___x_1757_; 
v_val_1756_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1757_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1756_);
lean_dec(v_val_1756_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText___boxed(lean_object* v_s_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_TSyntax_getVersoText(v_s_1758_);
lean_dec(v_s_1758_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object* v_s_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_1762_ = l_Lean_Syntax_isLit_x3f(v___x_1761_, v_s_1760_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v___x_1763_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1763_;
}
else
{
lean_object* v_val_1764_; 
v_val_1764_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_val_1764_);
lean_dec_ref_known(v___x_1762_, 1);
return v_val_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource___boxed(lean_object* v_s_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_TSyntax_getVersoTextSource(v_s_1765_);
lean_dec(v_s_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName(lean_object* v_s_1767_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_Lean_Doc_versoRefKind));
v___x_1769_ = l_Lean_Syntax_isLit_x3f(v___x_1768_, v_s_1767_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1770_;
}
else
{
lean_object* v_val_1771_; 
v_val_1771_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v___x_1769_, 1);
return v_val_1771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName___boxed(lean_object* v_s_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_TSyntax_getVersoRefName(v_s_1772_);
lean_dec(v_s_1772_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object* v_s_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_Doc_versoLinkUrlKind));
v___x_1776_ = l_Lean_Syntax_isLit_x3f(v___x_1775_, v_s_1774_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1777_;
}
else
{
lean_object* v_val_1778_; lean_object* v___x_1779_; 
v_val_1778_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1779_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1778_);
lean_dec(v_val_1778_);
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl___boxed(lean_object* v_s_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_1780_);
lean_dec(v_s_1780_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object* v_s_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_Doc_versoLinkRefUrlKind));
v___x_1784_ = l_Lean_Syntax_isLit_x3f(v___x_1783_, v_s_1782_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v___x_1785_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1785_;
}
else
{
lean_object* v_val_1786_; 
v_val_1786_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_val_1786_);
lean_dec_ref_known(v___x_1784_, 1);
return v_val_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl___boxed(lean_object* v_s_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_1787_);
lean_dec(v_s_1787_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object* v_s_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_Doc_versoImageAltKind));
v___x_1791_ = l_Lean_Syntax_isLit_x3f(v___x_1790_, v_s_1789_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1792_;
}
else
{
lean_object* v_val_1793_; lean_object* v___x_1794_; 
v_val_1793_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1793_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1794_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1793_);
lean_dec(v_val_1793_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt___boxed(lean_object* v_s_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_TSyntax_getVersoImageAlt(v_s_1795_);
lean_dec(v_s_1795_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object* v_s_1797_){
_start:
{
lean_object* v___y_1799_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_Doc_versoCodeKind));
v___x_1812_ = l_Lean_Syntax_isLit_x3f(v___x_1811_, v_s_1797_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___y_1799_ = v___x_1813_;
goto v___jp_1798_;
}
else
{
lean_object* v_val_1814_; 
v_val_1814_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_val_1814_);
lean_dec_ref_known(v___x_1812_, 1);
v___y_1799_ = v_val_1814_;
goto v___jp_1798_;
}
v___jp_1798_:
{
uint8_t v___x_1800_; 
lean_inc_ref(v___y_1799_);
v___x_1800_ = l_Lean_Doc_versoCodeBoundarySpaces(v___y_1799_);
if (v___x_1800_ == 0)
{
return v___y_1799_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_string_utf8_byte_size(v___y_1799_);
lean_inc_ref_n(v___y_1799_, 2);
v___x_1804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1804_, 0, v___y_1799_);
lean_ctor_set(v___x_1804_, 1, v___x_1802_);
lean_ctor_set(v___x_1804_, 2, v___x_1803_);
v___x_1805_ = l_String_Slice_Pos_nextn(v___x_1804_, v___x_1802_, v___x_1801_);
lean_dec_ref_known(v___x_1804_, 3);
lean_inc(v___x_1805_);
v___x_1806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1806_, 0, v___y_1799_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
lean_ctor_set(v___x_1806_, 2, v___x_1803_);
v___x_1807_ = lean_nat_sub(v___x_1803_, v___x_1805_);
v___x_1808_ = l_String_Slice_Pos_prevn(v___x_1806_, v___x_1807_, v___x_1801_);
lean_dec_ref_known(v___x_1806_, 3);
v___x_1809_ = lean_nat_add(v___x_1805_, v___x_1808_);
lean_dec(v___x_1808_);
v___x_1810_ = lean_string_utf8_extract_fast(v___y_1799_, v___x_1805_, v___x_1809_);
lean_dec(v___x_1809_);
lean_dec(v___x_1805_);
lean_dec_ref(v___y_1799_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object* v_s_1815_){
_start:
{
lean_object* v_res_1816_; 
v_res_1816_ = l_Lean_TSyntax_getVersoCode(v_s_1815_);
lean_dec(v_s_1815_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLine(lean_object* v_s_1817_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_Doc_versoCodeBlockLineKind));
v___x_1819_ = l_Lean_Syntax_isLit_x3f(v___x_1818_, v_s_1817_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v___x_1820_; 
v___x_1820_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1820_;
}
else
{
lean_object* v_val_1821_; 
v_val_1821_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_val_1821_);
lean_dec_ref_known(v___x_1819_, 1);
return v_val_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLine___boxed(lean_object* v_s_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_TSyntax_getVersoCodeBlockLine(v_s_1822_);
lean_dec(v_s_1822_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object* v_s_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = l_Lean_Syntax_getArg(v_s_1824_, v___x_1825_);
v___x_1827_ = l_Lean_Syntax_getArgs(v___x_1826_);
lean_dec(v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object* v_s_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_1828_);
lean_dec(v_s_1828_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCodeBlock_spec__0(lean_object* v_as_1830_, size_t v_sz_1831_, size_t v_i_1832_, lean_object* v_b_1833_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_usize_dec_lt(v_i_1832_, v_sz_1831_);
if (v___x_1834_ == 0)
{
return v_b_1833_;
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; size_t v___x_1838_; size_t v___x_1839_; 
v_a_1835_ = lean_array_uget_borrowed(v_as_1830_, v_i_1832_);
v___x_1836_ = l_Lean_TSyntax_getVersoCodeBlockLine(v_a_1835_);
v___x_1837_ = lean_string_append(v_b_1833_, v___x_1836_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1832_, v___x_1838_);
v_i_1832_ = v___x_1839_;
v_b_1833_ = v___x_1837_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCodeBlock_spec__0___boxed(lean_object* v_as_1841_, lean_object* v_sz_1842_, lean_object* v_i_1843_, lean_object* v_b_1844_){
_start:
{
size_t v_sz_boxed_1845_; size_t v_i_boxed_1846_; lean_object* v_res_1847_; 
v_sz_boxed_1845_ = lean_unbox_usize(v_sz_1842_);
lean_dec(v_sz_1842_);
v_i_boxed_1846_ = lean_unbox_usize(v_i_1843_);
lean_dec(v_i_1843_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCodeBlock_spec__0(v_as_1841_, v_sz_boxed_1845_, v_i_boxed_1846_, v_b_1844_);
lean_dec_ref(v_as_1841_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object* v_s_1848_){
_start:
{
lean_object* v_out_1849_; lean_object* v___x_1850_; size_t v_sz_1851_; size_t v___x_1852_; lean_object* v___x_1853_; 
v_out_1849_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1850_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_1848_);
v_sz_1851_ = lean_array_size(v___x_1850_);
v___x_1852_ = ((size_t)0ULL);
v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCodeBlock_spec__0(v___x_1850_, v_sz_1851_, v___x_1852_, v_out_1849_);
lean_dec_ref(v___x_1850_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock___boxed(lean_object* v_s_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_1854_);
lean_dec(v_s_1854_);
return v_res_1855_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_str___closed__3(void){
_start:
{
uint8_t v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1864_ = 0;
v___x_1865_ = l_Lean_Parser_strLit;
v___x_1866_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___closed__2));
v___x_1867_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___closed__0));
v___x_1868_ = l_Lean_Parser_nodeWithAntiquot(v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_str(void){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_str___closed__3, &l_Lean_Doc_Parser_ArgVal_str___closed__3_once, _init_l_Lean_Doc_Parser_ArgVal_str___closed__3);
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_ident___closed__2(void){
_start:
{
uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1877_ = 0;
v___x_1878_ = l_Lean_Parser_ident;
v___x_1879_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___closed__1));
v___x_1880_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___closed__0));
v___x_1881_ = l_Lean_Parser_nodeWithAntiquot(v___x_1880_, v___x_1879_, v___x_1878_, v___x_1877_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_ident(void){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_ident___closed__2, &l_Lean_Doc_Parser_ArgVal_ident___closed__2_once, _init_l_Lean_Doc_Parser_ArgVal_ident___closed__2);
return v___x_1882_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_num___closed__2(void){
_start:
{
uint8_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1890_ = 0;
v___x_1891_ = l_Lean_Parser_numLit;
v___x_1892_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___closed__1));
v___x_1893_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___closed__0));
v___x_1894_ = l_Lean_Parser_nodeWithAntiquot(v___x_1893_, v___x_1892_, v___x_1891_, v___x_1890_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_num(void){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_num___closed__2, &l_Lean_Doc_Parser_ArgVal_num___closed__2_once, _init_l_Lean_Doc_Parser_ArgVal_num___closed__2);
return v___x_1895_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__2(void){
_start:
{
uint8_t v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = 1;
v___x_1903_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___closed__1));
v___x_1904_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___closed__0));
v___x_1905_ = l_Lean_Parser_mkAntiquot(v___x_1904_, v___x_1903_, v___x_1902_, v___x_1902_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = l_Lean_Doc_Parser_ArgVal_num;
v___x_1907_ = l_Lean_Doc_Parser_ArgVal_ident;
v___x_1908_ = l_Lean_Parser_orelse(v___x_1907_, v___x_1906_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__4(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__3, &l_Lean_Doc_Parser_argVal___closed__3_once, _init_l_Lean_Doc_Parser_argVal___closed__3);
v___x_1910_ = l_Lean_Doc_Parser_ArgVal_str;
v___x_1911_ = l_Lean_Parser_orelse(v___x_1910_, v___x_1909_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__5(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__4, &l_Lean_Doc_Parser_argVal___closed__4_once, _init_l_Lean_Doc_Parser_argVal___closed__4);
v___x_1913_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__2, &l_Lean_Doc_Parser_argVal___closed__2_once, _init_l_Lean_Doc_Parser_argVal___closed__2);
v___x_1914_ = l_Lean_Parser_withAntiquot(v___x_1913_, v___x_1912_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal(void){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__5, &l_Lean_Doc_Parser_argVal___closed__5_once, _init_l_Lean_Doc_Parser_argVal___closed__5);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_anon___closed__2(void){
_start:
{
uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1923_ = 0;
v___x_1924_ = l_Lean_Doc_Parser_argVal;
v___x_1925_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___closed__1));
v___x_1926_ = ((lean_object*)(l_Lean_Doc_Syntax_anon___closed__0));
v___x_1927_ = l_Lean_Parser_nodeWithAntiquot(v___x_1926_, v___x_1925_, v___x_1924_, v___x_1923_);
return v___x_1927_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_anon(void){
_start:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_anon___closed__2, &l_Lean_Doc_Parser_Arg_anon___closed__2_once, _init_l_Lean_Doc_Parser_Arg_anon___closed__2);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1(){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___closed__1));
v___x_1931_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0));
v___x_1932_ = l_Lean_addBuiltinDocString(v___x_1930_, v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
return v_res_1934_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__1(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__2));
v___x_1942_ = l_Lean_Parser_symbol(v___x_1941_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__2(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__5));
v___x_1944_ = l_Lean_Parser_symbol(v___x_1943_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__3(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = ((lean_object*)(l_Lean_Doc_Syntax_arg__val_quot___closed__13));
v___x_1946_ = l_Lean_Parser_symbol(v___x_1945_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__4(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__3, &l_Lean_Doc_Parser_Arg_named___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___closed__3);
v___x_1948_ = l_Lean_Doc_Parser_argVal;
v___x_1949_ = l_Lean_Parser_andthen(v___x_1948_, v___x_1947_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__5(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__4, &l_Lean_Doc_Parser_Arg_named___closed__4_once, _init_l_Lean_Doc_Parser_Arg_named___closed__4);
v___x_1951_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__2, &l_Lean_Doc_Parser_Arg_named___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named___closed__2);
v___x_1952_ = l_Lean_Parser_andthen(v___x_1951_, v___x_1950_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__6(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__5, &l_Lean_Doc_Parser_Arg_named___closed__5_once, _init_l_Lean_Doc_Parser_Arg_named___closed__5);
v___x_1954_ = l_Lean_Parser_ident;
v___x_1955_ = l_Lean_Parser_andthen(v___x_1954_, v___x_1953_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__7(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__6, &l_Lean_Doc_Parser_Arg_named___closed__6_once, _init_l_Lean_Doc_Parser_Arg_named___closed__6);
v___x_1957_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__1, &l_Lean_Doc_Parser_Arg_named___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named___closed__1);
v___x_1958_ = l_Lean_Parser_andthen(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__8(void){
_start:
{
uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1959_ = 0;
v___x_1960_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__7, &l_Lean_Doc_Parser_Arg_named___closed__7_once, _init_l_Lean_Doc_Parser_Arg_named___closed__7);
v___x_1961_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___closed__0));
v___x_1962_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__0));
v___x_1963_ = l_Lean_Parser_nodeWithAntiquot(v___x_1962_, v___x_1961_, v___x_1960_, v___x_1959_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named(void){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__8, &l_Lean_Doc_Parser_Arg_named___closed__8_once, _init_l_Lean_Doc_Parser_Arg_named___closed__8);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1(){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___closed__0));
v___x_1967_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_1968_ = l_Lean_addBuiltinDocString(v___x_1966_, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object* v_a_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
return v_res_1970_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__1(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = l_Lean_Doc_Parser_argVal;
v___x_1978_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__2, &l_Lean_Doc_Parser_Arg_named___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named___closed__2);
v___x_1979_ = l_Lean_Parser_andthen(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__2(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___closed__1, &l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__1);
v___x_1981_ = l_Lean_Parser_ident;
v___x_1982_ = l_Lean_Parser_andthen(v___x_1981_, v___x_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__3(void){
_start:
{
uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1983_ = 0;
v___x_1984_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___closed__2, &l_Lean_Doc_Parser_Arg_named__no__paren___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__2);
v___x_1985_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___closed__0));
v___x_1986_ = ((lean_object*)(l_Lean_Doc_Syntax_named__no__paren___closed__0));
v___x_1987_ = l_Lean_Parser_nodeWithAntiquot(v___x_1986_, v___x_1985_, v___x_1984_, v___x_1983_);
return v___x_1987_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren(void){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___closed__3, &l_Lean_Doc_Parser_Arg_named__no__paren___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__3);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1(){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___closed__0));
v___x_1991_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_1992_ = l_Lean_addBuiltinDocString(v___x_1990_, v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
return v_res_1994_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___closed__1(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__2));
v___x_2002_ = l_Lean_Parser_symbol(v___x_2001_);
return v___x_2002_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___closed__2(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = l_Lean_Parser_ident;
v___x_2004_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___closed__1, &l_Lean_Doc_Parser_Arg_flag__on___closed__1_once, _init_l_Lean_Doc_Parser_Arg_flag__on___closed__1);
v___x_2005_ = l_Lean_Parser_andthen(v___x_2004_, v___x_2003_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___closed__3(void){
_start:
{
uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2006_ = 0;
v___x_2007_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___closed__2, &l_Lean_Doc_Parser_Arg_flag__on___closed__2_once, _init_l_Lean_Doc_Parser_Arg_flag__on___closed__2);
v___x_2008_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___closed__0));
v___x_2009_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__0));
v___x_2010_ = l_Lean_Parser_nodeWithAntiquot(v___x_2009_, v___x_2008_, v___x_2007_, v___x_2006_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on(void){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___closed__3, &l_Lean_Doc_Parser_Arg_flag__on___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__on___closed__3);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1(){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___closed__0));
v___x_2014_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0));
v___x_2015_ = l_Lean_addBuiltinDocString(v___x_2013_, v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
return v_res_2017_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___closed__1(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__2));
v___x_2025_ = l_Lean_Parser_symbol(v___x_2024_);
return v___x_2025_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___closed__2(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2026_ = l_Lean_Parser_ident;
v___x_2027_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___closed__1, &l_Lean_Doc_Parser_Arg_flag__off___closed__1_once, _init_l_Lean_Doc_Parser_Arg_flag__off___closed__1);
v___x_2028_ = l_Lean_Parser_andthen(v___x_2027_, v___x_2026_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___closed__3(void){
_start:
{
uint8_t v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2029_ = 0;
v___x_2030_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___closed__2, &l_Lean_Doc_Parser_Arg_flag__off___closed__2_once, _init_l_Lean_Doc_Parser_Arg_flag__off___closed__2);
v___x_2031_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___closed__0));
v___x_2032_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__0));
v___x_2033_ = l_Lean_Parser_nodeWithAntiquot(v___x_2032_, v___x_2031_, v___x_2030_, v___x_2029_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off(void){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___closed__3, &l_Lean_Doc_Parser_Arg_flag__off___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__off___closed__3);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1(){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___closed__0));
v___x_2037_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0));
v___x_2038_ = l_Lean_addBuiltinDocString(v___x_2036_, v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
return v_res_2040_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__2(void){
_start:
{
uint8_t v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2047_ = 1;
v___x_2048_ = ((lean_object*)(l_Lean_Doc_Parser_arg___closed__1));
v___x_2049_ = ((lean_object*)(l_Lean_Doc_Parser_arg___closed__0));
v___x_2050_ = l_Lean_Parser_mkAntiquot(v___x_2049_, v___x_2048_, v___x_2047_, v___x_2047_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__3(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = l_Lean_Doc_Parser_Arg_named__no__paren;
v___x_2052_ = l_Lean_Parser_atomic(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__4(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = l_Lean_Doc_Parser_Arg_anon;
v___x_2054_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__3, &l_Lean_Doc_Parser_arg___closed__3_once, _init_l_Lean_Doc_Parser_arg___closed__3);
v___x_2055_ = l_Lean_Parser_orelse(v___x_2054_, v___x_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__5(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__4, &l_Lean_Doc_Parser_arg___closed__4_once, _init_l_Lean_Doc_Parser_arg___closed__4);
v___x_2057_ = l_Lean_Doc_Parser_Arg_flag__off;
v___x_2058_ = l_Lean_Parser_orelse(v___x_2057_, v___x_2056_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__6(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__5, &l_Lean_Doc_Parser_arg___closed__5_once, _init_l_Lean_Doc_Parser_arg___closed__5);
v___x_2060_ = l_Lean_Doc_Parser_Arg_flag__on;
v___x_2061_ = l_Lean_Parser_orelse(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__7(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__6, &l_Lean_Doc_Parser_arg___closed__6_once, _init_l_Lean_Doc_Parser_arg___closed__6);
v___x_2063_ = l_Lean_Doc_Parser_Arg_named;
v___x_2064_ = l_Lean_Parser_orelse(v___x_2063_, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__8(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__7, &l_Lean_Doc_Parser_arg___closed__7_once, _init_l_Lean_Doc_Parser_arg___closed__7);
v___x_2066_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__2, &l_Lean_Doc_Parser_arg___closed__2_once, _init_l_Lean_Doc_Parser_arg___closed__2);
v___x_2067_ = l_Lean_Parser_withAntiquot(v___x_2066_, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg(void){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__8, &l_Lean_Doc_Parser_arg___closed__8_once, _init_l_Lean_Doc_Parser_arg___closed__8);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___closed__2(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__3, &l_Lean_Doc_Parser_Arg_named___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___closed__3);
v___x_2077_ = l_Lean_Doc_Parser_versoLinkUrl;
v___x_2078_ = l_Lean_Parser_andthen(v___x_2077_, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___closed__3(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___closed__2, &l_Lean_Doc_Parser_LinkTarget_url___closed__2_once, _init_l_Lean_Doc_Parser_LinkTarget_url___closed__2);
v___x_2080_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__1, &l_Lean_Doc_Parser_Arg_named___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named___closed__1);
v___x_2081_ = l_Lean_Parser_andthen(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___closed__4(void){
_start:
{
uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2082_ = 0;
v___x_2083_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___closed__3, &l_Lean_Doc_Parser_LinkTarget_url___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_url___closed__3);
v___x_2084_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___closed__1));
v___x_2085_ = ((lean_object*)(l_Lean_Doc_Syntax_url___closed__0));
v___x_2086_ = l_Lean_Parser_nodeWithAntiquot(v___x_2085_, v___x_2084_, v___x_2083_, v___x_2082_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url(void){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___closed__4, &l_Lean_Doc_Parser_LinkTarget_url___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_url___closed__4);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1(){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___closed__1));
v___x_2090_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0));
v___x_2091_ = l_Lean_addBuiltinDocString(v___x_2089_, v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
return v_res_2093_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__2));
v___x_2101_ = l_Lean_Parser_symbol(v___x_2100_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__2(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__5));
v___x_2103_ = l_Lean_Parser_symbol(v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__3(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__2, &l_Lean_Doc_Parser_LinkTarget_ref___closed__2_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__2);
v___x_2105_ = l_Lean_Doc_Parser_versoRef;
v___x_2106_ = l_Lean_Parser_andthen(v___x_2105_, v___x_2104_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__4(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__3, &l_Lean_Doc_Parser_LinkTarget_ref___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__3);
v___x_2108_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__1, &l_Lean_Doc_Parser_LinkTarget_ref___closed__1_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__1);
v___x_2109_ = l_Lean_Parser_andthen(v___x_2108_, v___x_2107_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__5(void){
_start:
{
uint8_t v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2110_ = 0;
v___x_2111_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__4, &l_Lean_Doc_Parser_LinkTarget_ref___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__4);
v___x_2112_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___closed__0));
v___x_2113_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__0));
v___x_2114_ = l_Lean_Parser_nodeWithAntiquot(v___x_2113_, v___x_2112_, v___x_2111_, v___x_2110_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref(void){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__5, &l_Lean_Doc_Parser_LinkTarget_ref___closed__5_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__5);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1(){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___closed__0));
v___x_2118_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0));
v___x_2119_ = l_Lean_addBuiltinDocString(v___x_2117_, v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
return v_res_2121_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___closed__2(void){
_start:
{
uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = 1;
v___x_2129_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___closed__1));
v___x_2130_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___closed__0));
v___x_2131_ = l_Lean_Parser_mkAntiquot(v___x_2130_, v___x_2129_, v___x_2128_, v___x_2128_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___closed__3(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_Doc_Parser_LinkTarget_ref;
v___x_2133_ = l_Lean_Doc_Parser_LinkTarget_url;
v___x_2134_ = l_Lean_Parser_orelse(v___x_2133_, v___x_2132_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___closed__4(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___closed__3, &l_Lean_Doc_Parser_linkTarget___closed__3_once, _init_l_Lean_Doc_Parser_linkTarget___closed__3);
v___x_2136_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___closed__2, &l_Lean_Doc_Parser_linkTarget___closed__2_once, _init_l_Lean_Doc_Parser_linkTarget___closed__2);
v___x_2137_ = l_Lean_Parser_withAntiquot(v___x_2136_, v___x_2135_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget(void){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___closed__4, &l_Lean_Doc_Parser_linkTarget___closed__4_once, _init_l_Lean_Doc_Parser_linkTarget___closed__4);
return v___x_2138_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
if (lean_obj_tag(v_x_2139_) == 0)
{
if (lean_obj_tag(v_x_2140_) == 0)
{
uint8_t v___x_2141_; 
v___x_2141_ = 1;
return v___x_2141_;
}
else
{
uint8_t v___x_2142_; 
v___x_2142_ = 0;
return v___x_2142_;
}
}
else
{
if (lean_obj_tag(v_x_2140_) == 0)
{
uint8_t v___x_2143_; 
v___x_2143_ = 0;
return v___x_2143_;
}
else
{
lean_object* v_val_2144_; lean_object* v_val_2145_; uint8_t v___x_2146_; 
v_val_2144_ = lean_ctor_get(v_x_2139_, 0);
v_val_2145_ = lean_ctor_get(v_x_2140_, 0);
v___x_2146_ = l_Lean_Parser_instBEqError_beq(v_val_2144_, v_val_2145_);
return v___x_2146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
uint8_t v_res_2149_; lean_object* v_r_2150_; 
v_res_2149_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_x_2147_, v_x_2148_);
lean_dec(v_x_2148_);
lean_dec(v_x_2147_);
v_r_2150_ = lean_box(v_res_2149_);
return v_r_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object* v_x_2151_, lean_object* v_st_2152_){
_start:
{
lean_inc_ref(v_st_2152_);
return v_st_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object* v_x_2153_, lean_object* v_st_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(v_x_2153_, v_st_2154_);
lean_dec_ref(v_st_2154_);
lean_dec_ref(v_x_2153_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2(lean_object* v_x_2156_, lean_object* v___f_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Parser_andthenFn(v_x_2156_, v___f_2157_, v___y_2158_, v___y_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT uint8_t l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(uint32_t v_head_2161_, uint32_t v_x_2162_){
_start:
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_uint32_dec_eq(v_x_2162_, v_head_2161_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed(lean_object* v_head_2164_, lean_object* v_x_2165_){
_start:
{
uint32_t v_head_310__boxed_2166_; uint32_t v_x_311__boxed_2167_; uint8_t v_res_2168_; lean_object* v_r_2169_; 
v_head_310__boxed_2166_ = lean_unbox_uint32(v_head_2164_);
lean_dec(v_head_2164_);
v_x_311__boxed_2167_ = lean_unbox_uint32(v_x_2165_);
lean_dec(v_x_2165_);
v_res_2168_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(v_head_310__boxed_2166_, v_x_311__boxed_2167_);
v_r_2169_ = lean_box(v_res_2168_);
return v_r_2169_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(uint32_t v_head_2170_, lean_object* v___f_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2175_ = lean_string_push(v___x_2174_, v_head_2170_);
v___x_2176_ = l_Lean_Parser_satisfyFn(v___f_2171_, v___x_2175_, v___y_2172_, v___y_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed(lean_object* v_head_2177_, lean_object* v___f_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint32_t v_head_319__boxed_2181_; lean_object* v_res_2182_; 
v_head_319__boxed_2181_ = lean_unbox_uint32(v_head_2177_);
lean_dec(v_head_2177_);
v_res_2182_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(v_head_319__boxed_2181_, v___f_2178_, v___y_2179_, v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object* v_x_2183_, lean_object* v_x_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
if (lean_obj_tag(v_x_2184_) == 0)
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_apply_2(v_x_2183_, v___y_2185_, v___y_2186_);
return v___x_2187_;
}
else
{
lean_object* v_head_2188_; lean_object* v_tail_2189_; lean_object* v___f_2190_; lean_object* v___f_2191_; lean_object* v___f_2192_; 
v_head_2188_ = lean_ctor_get(v_x_2184_, 0);
lean_inc_n(v_head_2188_, 2);
v_tail_2189_ = lean_ctor_get(v_x_2184_, 1);
lean_inc(v_tail_2189_);
lean_dec_ref_known(v_x_2184_, 2);
v___f_2190_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2190_, 0, v_head_2188_);
v___f_2191_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2191_, 0, v_head_2188_);
lean_closure_set(v___f_2191_, 1, v___f_2190_);
v___f_2192_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2), 4, 2);
lean_closure_set(v___f_2192_, 0, v_x_2183_);
lean_closure_set(v___f_2192_, 1, v___f_2191_);
v_x_2183_ = v___f_2192_;
v_x_2184_ = v_tail_2189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object* v_s_2195_, lean_object* v___f_2196_, lean_object* v_c_2197_, lean_object* v_st_2198_){
_start:
{
lean_object* v___x_2199_; lean_object* v_st_x27_2200_; lean_object* v_errorMsg_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
lean_inc_ref(v_s_2195_);
v___x_2199_ = lean_string_data(v_s_2195_);
lean_inc_ref(v_st_2198_);
v_st_x27_2200_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(v___f_2196_, v___x_2199_, v_c_2197_, v_st_2198_);
v_errorMsg_2201_ = lean_ctor_get(v_st_x27_2200_, 4);
lean_inc(v_errorMsg_2201_);
v___x_2202_ = lean_box(0);
v___x_2203_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2201_, v___x_2202_);
lean_dec(v_errorMsg_2201_);
if (v___x_2203_ == 0)
{
lean_object* v_pos_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_pos_2204_ = lean_ctor_get(v_st_2198_, 2);
lean_inc(v_pos_2204_);
lean_dec_ref(v_st_2198_);
v___x_2205_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2206_ = lean_string_append(v___x_2205_, v_s_2195_);
lean_dec_ref(v_s_2195_);
v___x_2207_ = lean_string_append(v___x_2206_, v___x_2205_);
v___x_2208_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_2200_, v___x_2207_, v_pos_2204_, v___x_2202_);
return v___x_2208_;
}
else
{
lean_dec_ref(v_st_2198_);
lean_dec_ref(v_s_2195_);
return v_st_x27_2200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2(lean_object* v___y_2209_){
_start:
{
lean_inc(v___y_2209_);
return v___y_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2___boxed(lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2(v___y_2210_);
lean_dec(v___y_2210_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3(lean_object* v___y_2212_){
_start:
{
lean_inc_ref(v___y_2212_);
return v___y_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3___boxed(lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3(v___y_2213_);
lean_dec_ref(v___y_2213_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object* v_s_2222_){
_start:
{
lean_object* v___f_2223_; lean_object* v___f_2224_; lean_object* v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___f_2223_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0));
v___f_2224_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1), 4, 2);
lean_closure_set(v___f_2224_, 0, v_s_2222_);
lean_closure_set(v___f_2224_, 1, v___f_2223_);
v___x_2225_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2226_ = 1;
v___x_2227_ = lean_box(v___x_2226_);
v___x_2228_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_2228_, 0, v___f_2224_);
lean_closure_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2225_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = l_Lean_Parser_tokenWithAntiquot(v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(uint32_t v_ch_2231_, uint32_t v_x_2232_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_uint32_dec_eq(v_x_2232_, v_ch_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed(lean_object* v_ch_2234_, lean_object* v_x_2235_){
_start:
{
uint32_t v_ch_boxed_2236_; uint32_t v_x_149__boxed_2237_; uint8_t v_res_2238_; lean_object* v_r_2239_; 
v_ch_boxed_2236_ = lean_unbox_uint32(v_ch_2234_);
lean_dec(v_ch_2234_);
v_x_149__boxed_2237_ = lean_unbox_uint32(v_x_2235_);
lean_dec(v_x_2235_);
v_res_2238_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(v_ch_boxed_2236_, v_x_149__boxed_2237_);
v_r_2239_ = lean_box(v_res_2238_);
return v_r_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(uint32_t v_ch_2241_, lean_object* v___f_2242_, lean_object* v_c_2243_, lean_object* v_st_2244_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_st_x27_2250_; lean_object* v_errorMsg_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2245_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2246_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2247_ = lean_string_push(v___x_2246_, v_ch_2241_);
v___x_2248_ = lean_string_append(v___x_2245_, v___x_2247_);
v___x_2249_ = lean_string_append(v___x_2248_, v___x_2245_);
lean_inc_ref(v_st_2244_);
v_st_x27_2250_ = l_Lean_Parser_takeWhile1Fn(v___f_2242_, v___x_2249_, v_c_2243_, v_st_2244_);
v_errorMsg_2251_ = lean_ctor_get(v_st_x27_2250_, 4);
lean_inc(v_errorMsg_2251_);
v___x_2252_ = lean_box(0);
v___x_2253_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2251_, v___x_2252_);
lean_dec(v_errorMsg_2251_);
if (v___x_2253_ == 0)
{
lean_object* v_pos_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_pos_2254_ = lean_ctor_get(v_st_2244_, 2);
lean_inc(v_pos_2254_);
lean_dec_ref(v_st_2244_);
v___x_2255_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0));
v___x_2256_ = lean_string_append(v___x_2255_, v___x_2247_);
lean_dec_ref(v___x_2247_);
v___x_2257_ = lean_string_append(v___x_2256_, v___x_2245_);
v___x_2258_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_2250_, v___x_2257_, v_pos_2254_, v___x_2252_);
return v___x_2258_;
}
else
{
lean_dec_ref(v___x_2247_);
lean_dec_ref(v_st_2244_);
return v_st_x27_2250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed(lean_object* v_ch_2259_, lean_object* v___f_2260_, lean_object* v_c_2261_, lean_object* v_st_2262_){
_start:
{
uint32_t v_ch_boxed_2263_; lean_object* v_res_2264_; 
v_ch_boxed_2263_ = lean_unbox_uint32(v_ch_2259_);
lean_dec(v_ch_2259_);
v_res_2264_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(v_ch_boxed_2263_, v___f_2260_, v_c_2261_, v_st_2262_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(uint32_t v_ch_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___f_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2266_ = lean_box_uint32(v_ch_2265_);
v___f_2267_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2267_, 0, v___x_2266_);
v___x_2268_ = lean_box_uint32(v_ch_2265_);
v___f_2269_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2269_, 0, v___x_2268_);
lean_closure_set(v___f_2269_, 1, v___f_2267_);
v___x_2270_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2271_ = 1;
v___x_2272_ = lean_box(v___x_2271_);
v___x_2273_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_2273_, 0, v___f_2269_);
lean_closure_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2270_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = l_Lean_Parser_tokenWithAntiquot(v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___boxed(lean_object* v_ch_2276_){
_start:
{
uint32_t v_ch_boxed_2277_; lean_object* v_res_2278_; 
v_ch_boxed_2277_ = lean_unbox_uint32(v_ch_2276_);
lean_dec(v_ch_2276_);
v_res_2278_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v_ch_boxed_2277_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(lean_object* v_c_2280_, lean_object* v_s_2281_){
_start:
{
lean_object* v_toInputContext_2282_; lean_object* v_pos_2283_; uint8_t v___x_2284_; 
v_toInputContext_2282_ = lean_ctor_get(v_c_2280_, 0);
v_pos_2283_ = lean_ctor_get(v_s_2281_, 2);
v___x_2284_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2282_, v_pos_2283_);
if (v___x_2284_ == 0)
{
lean_object* v_inputString_2285_; uint32_t v_ch_2286_; uint32_t v___x_2287_; uint8_t v___x_2288_; 
lean_inc(v_pos_2283_);
v_inputString_2285_ = lean_ctor_get(v_toInputContext_2282_, 0);
v_ch_2286_ = lean_string_utf8_get_fast(v_inputString_2285_, v_pos_2283_);
v___x_2287_ = 42;
v___x_2288_ = lean_uint32_dec_eq(v_ch_2286_, v___x_2287_);
if (v___x_2288_ == 0)
{
uint32_t v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = 45;
v___x_2290_ = lean_uint32_dec_eq(v_ch_2286_, v___x_2289_);
if (v___x_2290_ == 0)
{
uint32_t v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = 43;
v___x_2292_ = lean_uint32_dec_eq(v_ch_2286_, v___x_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0));
v___x_2294_ = lean_box(0);
v___x_2295_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2281_, v___x_2293_, v_pos_2283_, v___x_2294_);
return v___x_2295_;
}
else
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2281_, v_c_2280_, v_pos_2283_);
lean_dec(v_pos_2283_);
return v___x_2296_;
}
}
else
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2281_, v_c_2280_, v_pos_2283_);
lean_dec(v_pos_2283_);
return v___x_2297_;
}
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2281_, v_c_2280_, v_pos_2283_);
lean_dec(v_pos_2283_);
return v___x_2298_;
}
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = lean_box(0);
v___x_2300_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2281_, v___x_2299_);
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed(lean_object* v_c_2301_, lean_object* v_s_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(v_c_2301_, v_s_2302_);
lean_dec_ref(v_c_2301_);
return v_res_2303_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2));
v___x_2313_ = l_Lean_Parser_tokenWithAntiquot(v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom(void){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3);
return v___x_2314_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(uint32_t v_x_2315_){
_start:
{
uint32_t v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = 48;
v___x_2317_ = lean_uint32_dec_le(v___x_2316_, v_x_2315_);
if (v___x_2317_ == 0)
{
return v___x_2317_;
}
else
{
uint32_t v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = 57;
v___x_2319_ = lean_uint32_dec_le(v_x_2315_, v___x_2318_);
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed(lean_object* v_x_2320_){
_start:
{
uint32_t v_x_229__boxed_2321_; uint8_t v_res_2322_; lean_object* v_r_2323_; 
v_x_229__boxed_2321_ = lean_unbox_uint32(v_x_2320_);
lean_dec(v_x_2320_);
v_res_2322_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(v_x_229__boxed_2321_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(uint32_t v_c_2324_){
_start:
{
uint32_t v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = 46;
v___x_2326_ = lean_uint32_dec_eq(v_c_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
uint32_t v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = 41;
v___x_2328_ = lean_uint32_dec_eq(v_c_2324_, v___x_2327_);
return v___x_2328_;
}
else
{
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed(lean_object* v_c_2329_){
_start:
{
uint32_t v_c_boxed_2330_; uint8_t v_res_2331_; lean_object* v_r_2332_; 
v_c_boxed_2330_ = lean_unbox_uint32(v_c_2329_);
lean_dec(v_c_2329_);
v_res_2331_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(v_c_boxed_2330_);
v_r_2332_ = lean_box(v_res_2331_);
return v_r_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(lean_object* v___f_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0));
v___x_2338_ = l_Lean_Parser_satisfyFn(v___f_2334_, v___x_2337_, v___y_2335_, v___y_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed(lean_object* v___f_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(v___f_2339_, v___y_2340_, v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3(lean_object* v___f_2345_, lean_object* v___f_2346_, lean_object* v_c_2347_, lean_object* v_s_2348_){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_s_x27_2351_; lean_object* v_errorMsg_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2349_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0));
v___x_2350_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhile1Fn), 4, 2);
lean_closure_set(v___x_2350_, 0, v___f_2345_);
lean_closure_set(v___x_2350_, 1, v___x_2349_);
lean_inc_ref(v_s_2348_);
v_s_x27_2351_ = l_Lean_Parser_andthenFn(v___x_2350_, v___f_2346_, v_c_2347_, v_s_2348_);
v_errorMsg_2352_ = lean_ctor_get(v_s_x27_2351_, 4);
lean_inc(v_errorMsg_2352_);
v___x_2353_ = lean_box(0);
v___x_2354_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2352_, v___x_2353_);
lean_dec(v_errorMsg_2352_);
if (v___x_2354_ == 0)
{
lean_object* v_pos_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_pos_2355_ = lean_ctor_get(v_s_2348_, 2);
lean_inc(v_pos_2355_);
lean_dec_ref(v_s_2348_);
v___x_2356_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1));
v___x_2357_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_x27_2351_, v___x_2356_, v_pos_2355_, v___x_2353_);
return v___x_2357_;
}
else
{
lean_dec_ref(v_s_2348_);
return v_s_x27_2351_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5));
v___x_2373_ = l_Lean_Parser_tokenWithAntiquot(v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom(void){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object* v_c_2375_){
_start:
{
lean_object* v_toInputContext_2376_; lean_object* v_toParserModuleContext_2377_; lean_object* v_toCacheableParserContext_2378_; lean_object* v_tokens_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2388_; 
v_toInputContext_2376_ = lean_ctor_get(v_c_2375_, 0);
v_toParserModuleContext_2377_ = lean_ctor_get(v_c_2375_, 1);
v_toCacheableParserContext_2378_ = lean_ctor_get(v_c_2375_, 2);
v_tokens_2379_ = lean_ctor_get(v_c_2375_, 3);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_c_2375_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2381_ = v_c_2375_;
v_isShared_2382_ = v_isSharedCheck_2388_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_tokens_2379_);
lean_inc(v_toCacheableParserContext_2378_);
lean_inc(v_toParserModuleContext_2377_);
lean_inc(v_toInputContext_2376_);
lean_dec(v_c_2375_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2388_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2383_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__2));
v___x_2384_ = l_Lean_Data_Trie_insert___redArg(v_tokens_2379_, v___x_2383_, v___x_2383_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 3, v___x_2384_);
v___x_2386_ = v___x_2381_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_toInputContext_2376_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_toParserModuleContext_2377_);
lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_toCacheableParserContext_2378_);
lean_ctor_set(v_reuseFailAlloc_2387_, 3, v___x_2384_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2(void){
_start:
{
uint8_t v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2395_ = 0;
v___x_2396_ = 1;
v___x_2397_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1));
v___x_2398_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__4));
v___x_2399_ = l_Lean_Parser_mkAntiquot(v___x_2398_, v___x_2397_, v___x_2396_, v___x_2395_);
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__17, &l_Lean_Doc_Syntax_metadataContents___closed__17_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__17);
v___x_2401_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2);
v___x_2402_ = l_Lean_Parser_withAntiquot(v___x_2401_, v___x_2400_);
return v___x_2402_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit(void){
_start:
{
lean_object* v___x_2404_; lean_object* v_fn_2405_; lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2404_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3);
v_fn_2405_ = lean_ctor_get(v___x_2404_, 1);
v___f_2406_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__4));
v___x_2407_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
lean_inc_ref(v_fn_2405_);
v___x_2408_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn), 4, 2);
lean_closure_set(v___x_2408_, 0, v___f_2406_);
lean_closure_set(v___x_2408_, 1, v_fn_2405_);
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___closed__2(void){
_start:
{
uint32_t v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = 35;
v___x_2417_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2416_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___closed__3(void){
_start:
{
uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2418_ = 0;
v___x_2419_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___closed__2, &l_Lean_Doc_Parser_headerMarker___closed__2_once, _init_l_Lean_Doc_Parser_headerMarker___closed__2);
v___x_2420_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___closed__1));
v___x_2421_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___closed__0));
v___x_2422_ = l_Lean_Parser_nodeWithAntiquot(v___x_2421_, v___x_2420_, v___x_2419_, v___x_2418_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___closed__3, &l_Lean_Doc_Parser_headerMarker___closed__3_once, _init_l_Lean_Doc_Parser_headerMarker___closed__3);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___closed__2(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom;
v___x_2431_ = l_Lean_Parser_atomic(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___closed__3(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom;
v___x_2433_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___closed__2, &l_Lean_Doc_Parser_listMarker___closed__2_once, _init_l_Lean_Doc_Parser_listMarker___closed__2);
v___x_2434_ = l_Lean_Parser_orelse(v___x_2433_, v___x_2432_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___closed__4(void){
_start:
{
uint8_t v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2435_ = 0;
v___x_2436_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___closed__3, &l_Lean_Doc_Parser_listMarker___closed__3_once, _init_l_Lean_Doc_Parser_listMarker___closed__3);
v___x_2437_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__1));
v___x_2438_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__0));
v___x_2439_ = l_Lean_Parser_nodeWithAntiquot(v___x_2438_, v___x_2437_, v___x_2436_, v___x_2435_);
return v___x_2439_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker(void){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___closed__4, &l_Lean_Doc_Parser_listMarker___closed__4_once, _init_l_Lean_Doc_Parser_listMarker___closed__4);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0(void){
_start:
{
uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2441_ = 0;
v___x_2442_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom;
v___x_2443_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__1));
v___x_2444_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__0));
v___x_2445_ = l_Lean_Parser_nodeWithAntiquot(v___x_2444_, v___x_2443_, v___x_2442_, v___x_2441_);
return v___x_2445_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker(void){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0(void){
_start:
{
uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2447_ = 0;
v___x_2448_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom;
v___x_2449_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__1));
v___x_2450_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__0));
v___x_2451_ = l_Lean_Parser_nodeWithAntiquot(v___x_2450_, v___x_2449_, v___x_2448_, v___x_2447_);
return v___x_2451_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker(void){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0);
return v___x_2452_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(uint32_t v_x_2453_){
_start:
{
uint32_t v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = 58;
v___x_2455_ = lean_uint32_dec_eq(v_x_2453_, v___x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed(lean_object* v_x_2456_){
_start:
{
uint32_t v_x_81__boxed_2457_; uint8_t v_res_2458_; lean_object* v_r_2459_; 
v_x_81__boxed_2457_ = lean_unbox_uint32(v_x_2456_);
lean_dec(v_x_2456_);
v_res_2458_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(v_x_81__boxed_2457_);
v_r_2459_ = lean_box(v_res_2458_);
return v_r_2459_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = ((lean_object*)(l_Lean_Doc_Syntax_desc___closed__2));
v___x_2462_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2));
v___x_2471_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__4));
v___x_2472_ = l_Lean_Parser_notFollowedBy(v___x_2471_, v___x_2470_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5);
v___x_2474_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1);
v___x_2475_ = l_Lean_Parser_andthen(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6);
v___x_2477_ = l_Lean_Parser_atomic(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker(void){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = 95;
v___x_2486_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2487_ = 0;
v___x_2488_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___closed__2, &l_Lean_Doc_Parser_emphDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_emphDelimiter___closed__2);
v___x_2489_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___closed__1));
v___x_2490_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___closed__0));
v___x_2491_ = l_Lean_Parser_nodeWithAntiquot(v___x_2490_, v___x_2489_, v___x_2488_, v___x_2487_);
return v___x_2491_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter(void){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___closed__3, &l_Lean_Doc_Parser_emphDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_emphDelimiter___closed__3);
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = 42;
v___x_2500_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2499_);
return v___x_2500_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2501_ = 0;
v___x_2502_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___closed__2, &l_Lean_Doc_Parser_boldDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_boldDelimiter___closed__2);
v___x_2503_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___closed__1));
v___x_2504_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___closed__0));
v___x_2505_ = l_Lean_Parser_nodeWithAntiquot(v___x_2504_, v___x_2503_, v___x_2502_, v___x_2501_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter(void){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___closed__3, &l_Lean_Doc_Parser_boldDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_boldDelimiter___closed__3);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = 96;
v___x_2514_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2513_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2515_ = 0;
v___x_2516_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___closed__2, &l_Lean_Doc_Parser_codeDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___closed__2);
v___x_2517_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___closed__1));
v___x_2518_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___closed__0));
v___x_2519_ = l_Lean_Parser_nodeWithAntiquot(v___x_2518_, v___x_2517_, v___x_2516_, v___x_2515_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter(void){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___closed__3, &l_Lean_Doc_Parser_codeDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_codeDelimiter___closed__3);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeBlockFence___closed__2(void){
_start:
{
uint8_t v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2527_ = 0;
v___x_2528_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___closed__2, &l_Lean_Doc_Parser_codeDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___closed__2);
v___x_2529_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___closed__1));
v___x_2530_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___closed__0));
v___x_2531_ = l_Lean_Parser_nodeWithAntiquot(v___x_2530_, v___x_2529_, v___x_2528_, v___x_2527_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeBlockFence(void){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_obj_once(&l_Lean_Doc_Parser_codeBlockFence___closed__2, &l_Lean_Doc_Parser_codeBlockFence___closed__2_once, _init_l_Lean_Doc_Parser_codeBlockFence___closed__2);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___closed__3(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___closed__2));
v___x_2541_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2540_);
return v___x_2541_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___closed__4(void){
_start:
{
uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2542_ = 0;
v___x_2543_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___closed__3, &l_Lean_Doc_Parser_inlineMathMarker___closed__3_once, _init_l_Lean_Doc_Parser_inlineMathMarker___closed__3);
v___x_2544_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___closed__1));
v___x_2545_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___closed__0));
v___x_2546_ = l_Lean_Parser_nodeWithAntiquot(v___x_2545_, v___x_2544_, v___x_2543_, v___x_2542_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker(void){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___closed__4, &l_Lean_Doc_Parser_inlineMathMarker___closed__4_once, _init_l_Lean_Doc_Parser_inlineMathMarker___closed__4);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___closed__3(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___closed__2));
v___x_2556_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2555_);
return v___x_2556_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___closed__4(void){
_start:
{
uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2557_ = 0;
v___x_2558_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___closed__3, &l_Lean_Doc_Parser_displayMathMarker___closed__3_once, _init_l_Lean_Doc_Parser_displayMathMarker___closed__3);
v___x_2559_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___closed__1));
v___x_2560_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___closed__0));
v___x_2561_ = l_Lean_Parser_nodeWithAntiquot(v___x_2560_, v___x_2559_, v___x_2558_, v___x_2557_);
return v___x_2561_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker(void){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___closed__4, &l_Lean_Doc_Parser_displayMathMarker___closed__4_once, _init_l_Lean_Doc_Parser_displayMathMarker___closed__4);
return v___x_2562_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = 58;
v___x_2570_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2569_);
return v___x_2570_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2571_ = 0;
v___x_2572_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___closed__2, &l_Lean_Doc_Parser_directiveDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_directiveDelimiter___closed__2);
v___x_2573_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___closed__1));
v___x_2574_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___closed__0));
v___x_2575_ = l_Lean_Parser_nodeWithAntiquot(v___x_2574_, v___x_2573_, v___x_2572_, v___x_2571_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter(void){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___closed__3, &l_Lean_Doc_Parser_directiveDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_directiveDelimiter___closed__3);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(lean_object* v_x_2577_){
_start:
{
if (lean_obj_tag(v_x_2577_) == 1)
{
lean_object* v_args_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v_args_2578_ = lean_ctor_get(v_x_2577_, 2);
v___x_2579_ = lean_array_get_size(v_args_2578_);
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_nat_dec_eq(v___x_2579_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_box(0);
return v___x_2582_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_unsigned_to_nat(0u);
v___x_2584_ = lean_array_fget_borrowed(v_args_2578_, v___x_2583_);
if (lean_obj_tag(v___x_2584_) == 2)
{
lean_object* v_val_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_val_2585_ = lean_ctor_get(v___x_2584_, 1);
v___x_2586_ = lean_string_length(v_val_2585_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
else
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_box(0);
return v___x_2588_;
}
}
}
else
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_box(0);
return v___x_2589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength___boxed(lean_object* v_x_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_x_2590_);
lean_dec(v_x_2590_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(uint32_t v_ch_2592_, lean_object* v_x_2593_, lean_object* v_x_2594_){
_start:
{
lean_object* v_zero_2595_; uint8_t v_isZero_2596_; 
v_zero_2595_ = lean_unsigned_to_nat(0u);
v_isZero_2596_ = lean_nat_dec_eq(v_x_2593_, v_zero_2595_);
if (v_isZero_2596_ == 1)
{
lean_dec(v_x_2593_);
return v_x_2594_;
}
else
{
lean_object* v_one_2597_; lean_object* v_n_2598_; lean_object* v___x_2599_; 
v_one_2597_ = lean_unsigned_to_nat(1u);
v_n_2598_ = lean_nat_sub(v_x_2593_, v_one_2597_);
lean_dec(v_x_2593_);
v___x_2599_ = lean_string_push(v_x_2594_, v_ch_2592_);
v_x_2593_ = v_n_2598_;
v_x_2594_ = v___x_2599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0___boxed(lean_object* v_ch_2601_, lean_object* v_x_2602_, lean_object* v_x_2603_){
_start:
{
uint32_t v_ch_boxed_2604_; lean_object* v_res_2605_; 
v_ch_boxed_2604_ = lean_unbox_uint32(v_ch_2601_);
lean_dec(v_ch_2601_);
v_res_2605_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_boxed_2604_, v_x_2602_, v_x_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(lean_object* v_delim_2608_, uint32_t v_ch_2609_, lean_object* v_contents_2610_, lean_object* v_c_2611_, lean_object* v_s_2612_){
_start:
{
lean_object* v_fn_2613_; lean_object* v_s_2614_; lean_object* v_stxStack_2615_; lean_object* v_errorMsg_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_fn_2613_ = lean_ctor_get(v_delim_2608_, 1);
lean_inc_ref_n(v_fn_2613_, 2);
lean_dec_ref(v_delim_2608_);
lean_inc_ref(v_c_2611_);
v_s_2614_ = lean_apply_2(v_fn_2613_, v_c_2611_, v_s_2612_);
v_stxStack_2615_ = lean_ctor_get(v_s_2614_, 0);
lean_inc_ref(v_stxStack_2615_);
v_errorMsg_2616_ = lean_ctor_get(v_s_2614_, 4);
lean_inc(v_errorMsg_2616_);
v___x_2617_ = lean_box(0);
v___x_2618_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2616_, v___x_2617_);
lean_dec(v_errorMsg_2616_);
if (v___x_2618_ == 0)
{
lean_dec_ref(v_stxStack_2615_);
lean_dec_ref(v_fn_2613_);
lean_dec_ref(v_c_2611_);
lean_dec_ref(v_contents_2610_);
return v_s_2614_;
}
else
{
lean_object* v_fn_2619_; lean_object* v_s_2620_; lean_object* v_pos_2621_; lean_object* v_errorMsg_2622_; uint8_t v___x_2623_; 
v_fn_2619_ = lean_ctor_get(v_contents_2610_, 1);
lean_inc_ref(v_fn_2619_);
lean_dec_ref(v_contents_2610_);
lean_inc_ref(v_c_2611_);
v_s_2620_ = lean_apply_2(v_fn_2619_, v_c_2611_, v_s_2614_);
v_pos_2621_ = lean_ctor_get(v_s_2620_, 2);
lean_inc(v_pos_2621_);
v_errorMsg_2622_ = lean_ctor_get(v_s_2620_, 4);
lean_inc(v_errorMsg_2622_);
v___x_2623_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2622_, v___x_2617_);
lean_dec(v_errorMsg_2622_);
if (v___x_2623_ == 0)
{
lean_dec(v_pos_2621_);
lean_dec_ref(v_stxStack_2615_);
lean_dec_ref(v_fn_2613_);
lean_dec_ref(v_c_2611_);
return v_s_2620_;
}
else
{
lean_object* v_s_2624_; lean_object* v_stxStack_2625_; lean_object* v_errorMsg_2626_; uint8_t v___x_2627_; 
v_s_2624_ = lean_apply_2(v_fn_2613_, v_c_2611_, v_s_2620_);
v_stxStack_2625_ = lean_ctor_get(v_s_2624_, 0);
lean_inc_ref(v_stxStack_2625_);
v_errorMsg_2626_ = lean_ctor_get(v_s_2624_, 4);
lean_inc(v_errorMsg_2626_);
v___x_2627_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2626_, v___x_2617_);
lean_dec(v_errorMsg_2626_);
if (v___x_2627_ == 0)
{
lean_dec_ref(v_stxStack_2625_);
lean_dec(v_pos_2621_);
lean_dec_ref(v_stxStack_2615_);
return v_s_2624_;
}
else
{
lean_object* v_opener_2628_; lean_object* v___x_2629_; 
v_opener_2628_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2615_);
lean_dec_ref(v_stxStack_2615_);
v___x_2629_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_opener_2628_);
lean_dec(v_opener_2628_);
if (lean_obj_tag(v___x_2629_) == 1)
{
lean_object* v_val_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_val_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_val_2630_);
lean_dec_ref_known(v___x_2629_, 1);
v___x_2631_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2625_);
lean_dec_ref(v_stxStack_2625_);
v___x_2632_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v___x_2631_);
lean_dec(v___x_2631_);
if (lean_obj_tag(v___x_2632_) == 1)
{
lean_object* v_val_2633_; uint8_t v___x_2634_; 
v_val_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = lean_nat_dec_eq(v_val_2630_, v_val_2633_);
lean_dec(v_val_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2635_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2636_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2637_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_2609_, v_val_2630_, v___x_2636_);
v___x_2638_ = lean_string_append(v___x_2635_, v___x_2637_);
v___x_2639_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0));
v___x_2640_ = lean_string_append(v___x_2638_, v___x_2639_);
v___x_2641_ = lean_string_append(v___x_2640_, v___x_2637_);
lean_dec_ref(v___x_2637_);
v___x_2642_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1));
v___x_2643_ = lean_string_append(v___x_2641_, v___x_2642_);
v___x_2644_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2624_, v___x_2643_, v_pos_2621_, v___x_2617_);
return v___x_2644_;
}
else
{
lean_dec(v_val_2630_);
lean_dec(v_pos_2621_);
return v_s_2624_;
}
}
else
{
lean_dec(v___x_2632_);
lean_dec(v_val_2630_);
lean_dec(v_pos_2621_);
return v_s_2624_;
}
}
else
{
lean_dec(v___x_2629_);
lean_dec_ref(v_stxStack_2625_);
lean_dec(v_pos_2621_);
return v_s_2624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed(lean_object* v_delim_2645_, lean_object* v_ch_2646_, lean_object* v_contents_2647_, lean_object* v_c_2648_, lean_object* v_s_2649_){
_start:
{
uint32_t v_ch_boxed_2650_; lean_object* v_res_2651_; 
v_ch_boxed_2650_ = lean_unbox_uint32(v_ch_2646_);
lean_dec(v_ch_2646_);
v_res_2651_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(v_delim_2645_, v_ch_boxed_2650_, v_contents_2647_, v_c_2648_, v_s_2649_);
return v_res_2651_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = 96;
v___x_2660_ = lean_box_uint32(v___x_2659_);
return v___x_2660_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = l_Lean_Doc_Parser_versoCode;
v___x_2662_ = l_Lean_Doc_Parser_codeDelimiter;
v___x_2663_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1;
v___x_2664_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_2664_, 0, v___x_2662_);
lean_closure_set(v___x_2664_, 1, v___x_2663_);
lean_closure_set(v___x_2664_, 2, v___x_2661_);
return v___x_2664_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2);
v___x_2666_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
lean_ctor_set(v___x_2667_, 1, v___x_2665_);
return v___x_2667_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4(void){
_start:
{
uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2668_ = 0;
v___x_2669_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3);
v___x_2670_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1));
v___x_2671_ = ((lean_object*)(l_Lean_Doc_Syntax_code___closed__0));
v___x_2672_ = l_Lean_Parser_nodeWithAntiquot(v___x_2671_, v___x_2670_, v___x_2669_, v___x_2668_);
return v___x_2672_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode(void){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4);
return v___x_2673_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1(void){
_start:
{
uint32_t v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = 10;
v___x_2681_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2680_);
return v___x_2681_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2(void){
_start:
{
uint8_t v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2682_ = 0;
v___x_2683_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1);
v___x_2684_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0));
v___x_2685_ = ((lean_object*)(l_Lean_Doc_Syntax_linebreak___closed__0));
v___x_2686_ = l_Lean_Parser_nodeWithAntiquot(v___x_2685_, v___x_2684_, v___x_2683_, v___x_2682_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___x_2689_; lean_object* v_fn_2690_; lean_object* v___x_2691_; 
v___x_2689_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2);
v_fn_2690_ = lean_ctor_get(v___x_2689_, 1);
lean_inc_ref(v_fn_2690_);
v___x_2691_ = lean_apply_2(v_fn_2690_, v_a_2687_, v_a_2688_);
return v___x_2691_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2699_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1));
v___x_2700_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2699_);
return v___x_2700_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3(void){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__5));
v___x_2702_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2701_);
return v___x_2702_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = l_Lean_Doc_Parser_linkTarget;
v___x_2704_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_2705_ = l_Lean_Parser_andthen(v___x_2704_, v___x_2703_);
return v___x_2705_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_2707_ = l_Lean_Doc_Parser_versoImageAlt;
v___x_2708_ = l_Lean_Parser_andthen(v___x_2707_, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5);
v___x_2710_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2);
v___x_2711_ = l_Lean_Parser_andthen(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7(void){
_start:
{
uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2712_ = 0;
v___x_2713_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6);
v___x_2714_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_2715_ = ((lean_object*)(l_Lean_Doc_Syntax_image___closed__0));
v___x_2716_ = l_Lean_Parser_nodeWithAntiquot(v___x_2715_, v___x_2714_, v___x_2713_, v___x_2712_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v___x_2719_; lean_object* v_fn_2720_; lean_object* v___x_2721_; 
v___x_2719_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7);
v_fn_2720_ = lean_ctor_get(v___x_2719_, 1);
lean_inc_ref(v_fn_2720_);
v___x_2721_ = lean_apply_2(v_fn_2720_, v_a_2717_, v_a_2718_);
return v___x_2721_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__2));
v___x_2729_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2728_);
return v___x_2729_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_2731_ = l_Lean_Doc_Parser_versoRef;
v___x_2732_ = l_Lean_Parser_andthen(v___x_2731_, v___x_2730_);
return v___x_2732_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2);
v___x_2734_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1);
v___x_2735_ = l_Lean_Parser_andthen(v___x_2734_, v___x_2733_);
return v___x_2735_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4(void){
_start:
{
uint8_t v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2736_ = 0;
v___x_2737_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3);
v___x_2738_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_2739_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote___closed__0));
v___x_2740_ = l_Lean_Parser_nodeWithAntiquot(v___x_2739_, v___x_2738_, v___x_2737_, v___x_2736_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v___x_2743_; lean_object* v_fn_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4);
v_fn_2744_ = lean_ctor_get(v___x_2743_, 1);
lean_inc_ref(v_fn_2744_);
v___x_2745_ = lean_apply_2(v_fn_2744_, v_a_2741_, v_a_2742_);
return v___x_2745_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
v___x_2753_ = l_Lean_Doc_Parser_inlineMathMarker;
v___x_2754_ = l_Lean_Parser_andthen(v___x_2753_, v___x_2752_);
return v___x_2754_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2(void){
_start:
{
uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2755_ = 0;
v___x_2756_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1);
v___x_2757_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_2758_ = ((lean_object*)(l_Lean_Doc_Syntax_inline__math___closed__0));
v___x_2759_ = l_Lean_Parser_nodeWithAntiquot(v___x_2758_, v___x_2757_, v___x_2756_, v___x_2755_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2762_; lean_object* v_fn_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2);
v_fn_2763_ = lean_ctor_get(v___x_2762_, 1);
lean_inc_ref(v_fn_2763_);
v___x_2764_ = lean_apply_2(v_fn_2763_, v_a_2760_, v_a_2761_);
return v___x_2764_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2771_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
v___x_2772_ = l_Lean_Doc_Parser_displayMathMarker;
v___x_2773_ = l_Lean_Parser_andthen(v___x_2772_, v___x_2771_);
return v___x_2773_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2(void){
_start:
{
uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2774_ = 0;
v___x_2775_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1);
v___x_2776_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_2777_ = ((lean_object*)(l_Lean_Doc_Syntax_display__math___closed__0));
v___x_2778_ = l_Lean_Parser_nodeWithAntiquot(v___x_2777_, v___x_2776_, v___x_2775_, v___x_2774_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot(lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2781_; lean_object* v_fn_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2);
v_fn_2782_ = lean_ctor_get(v___x_2781_, 1);
lean_inc_ref(v_fn_2782_);
v___x_2783_ = lean_apply_2(v_fn_2782_, v_a_2779_, v_a_2780_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2784_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot), 2, 0);
v___x_2785_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___x_2784_);
return v___x_2786_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
v___x_2788_ = l_Lean_Parser_atomic(v___x_2787_);
return v___x_2788_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2789_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot), 2, 0);
v___x_2790_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
lean_ctor_set(v___x_2791_, 1, v___x_2789_);
return v___x_2791_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
v___x_2793_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1);
v___x_2794_ = l_Lean_Parser_orelse(v___x_2793_, v___x_2792_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot(lean_object* v_a_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v_fn_2798_; lean_object* v___x_2799_; 
v___x_2797_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3);
v_fn_2798_ = lean_ctor_get(v___x_2797_, 1);
lean_inc_ref(v_fn_2798_);
v___x_2799_ = lean_apply_2(v_fn_2798_, v_a_2795_, v_a_2796_);
return v___x_2799_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1(void){
_start:
{
uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2806_ = 0;
v___x_2807_ = l_Lean_Doc_Parser_versoText;
v___x_2808_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0));
v___x_2809_ = ((lean_object*)(l_Lean_Doc_Syntax_text___closed__0));
v___x_2810_ = l_Lean_Parser_nodeWithAntiquot(v___x_2809_, v___x_2808_, v___x_2807_, v___x_2806_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v___x_2813_; lean_object* v_fn_2814_; lean_object* v___x_2815_; 
v___x_2813_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1);
v_fn_2814_ = lean_ctor_get(v___x_2813_, 1);
lean_inc_ref(v_fn_2814_);
v___x_2815_ = lean_apply_2(v_fn_2814_, v_a_2811_, v_a_2812_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object* v___y_2816_){
_start:
{
lean_inc(v___y_2816_);
return v___y_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(v___y_2817_);
lean_dec(v___y_2817_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object* v___y_2819_){
_start:
{
lean_inc_ref(v___y_2819_);
return v___y_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(v___y_2820_);
lean_dec_ref(v___y_2820_);
return v_res_2821_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = 42;
v___x_2835_ = lean_box_uint32(v___x_2834_);
return v___x_2835_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_2837_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
lean_ctor_set(v___x_2838_, 1, v___x_2836_);
return v___x_2838_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = 95;
v___x_2846_ = lean_box_uint32(v___x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v_fn_2862_; lean_object* v___x_2863_; 
v___x_2849_ = ((lean_object*)(l_Lean_Doc_Syntax_emph___closed__0));
v___x_2850_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_2851_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2852_ = l_Lean_Doc_Parser_emphDelimiter;
v___x_2853_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2851_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Lean_Parser_atomic(v___x_2854_);
v___x_2856_ = l_Lean_Parser_many(v___x_2855_);
v___x_2857_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
v___x_2858_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_2858_, 0, v___x_2852_);
lean_closure_set(v___x_2858_, 1, v___x_2857_);
lean_closure_set(v___x_2858_, 2, v___x_2856_);
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2851_);
lean_ctor_set(v___x_2859_, 1, v___x_2858_);
v___x_2860_ = 0;
v___x_2861_ = l_Lean_Parser_nodeWithAntiquot(v___x_2849_, v___x_2850_, v___x_2859_, v___x_2860_);
v_fn_2862_ = lean_ctor_get(v___x_2861_, 1);
lean_inc_ref(v_fn_2862_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = lean_apply_2(v_fn_2862_, v_a_2847_, v_a_2848_);
return v___x_2863_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1(void){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot), 2, 0);
v___x_2865_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___x_2864_);
return v___x_2866_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_2868_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2867_);
return v___x_2869_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__2));
v___x_2877_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; lean_object* v___x_2892_; lean_object* v_fn_2893_; lean_object* v___x_2894_; 
v___x_2880_ = ((lean_object*)(l_Lean_Doc_Syntax_link___closed__0));
v___x_2881_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_2882_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_2883_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2884_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2883_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = l_Lean_Parser_atomic(v___x_2885_);
v___x_2887_ = l_Lean_Parser_many(v___x_2886_);
v___x_2888_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_2889_ = l_Lean_Parser_andthen(v___x_2887_, v___x_2888_);
v___x_2890_ = l_Lean_Parser_andthen(v___x_2882_, v___x_2889_);
v___x_2891_ = 0;
v___x_2892_ = l_Lean_Parser_nodeWithAntiquot(v___x_2880_, v___x_2881_, v___x_2890_, v___x_2891_);
v_fn_2893_ = lean_ctor_get(v___x_2892_, 1);
lean_inc_ref(v_fn_2893_);
lean_dec_ref(v___x_2892_);
v___x_2894_ = lean_apply_2(v_fn_2893_, v_a_2878_, v_a_2879_);
return v___x_2894_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_2896_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___x_2895_);
return v___x_2897_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5(void){
_start:
{
uint8_t v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2903_ = 1;
v___x_2904_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4));
v___x_2905_ = ((lean_object*)(l_Lean_Doc_Syntax_inline_quot___closed__0));
v___x_2906_ = l_Lean_Parser_mkAntiquot(v___x_2905_, v___x_2904_, v___x_2903_, v___x_2903_);
return v___x_2906_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_2908_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___x_2907_);
return v___x_2909_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__6));
v___x_2917_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_Lean_Doc_Parser_arg;
v___x_2919_ = l_Lean_Parser_many(v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__7));
v___x_2921_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2920_);
return v___x_2921_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2925_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_2926_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2927_ = l_Lean_Parser_node(v___x_2926_, v___x_2925_);
return v___x_2927_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_2929_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2930_ = l_Lean_Parser_node(v___x_2929_, v___x_2928_);
return v___x_2930_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = l_Lean_Parser_skip;
v___x_2932_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2933_ = l_Lean_Parser_node(v___x_2932_, v___x_2931_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot(lean_object* v_a_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v_fn_2962_; lean_object* v___x_2963_; 
v___x_2936_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__0));
v___x_2937_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_2938_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1);
v___x_2939_ = l_Lean_Parser_ident;
v___x_2940_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_2941_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_2942_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6);
v___x_2943_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2944_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2943_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = l_Lean_Parser_atomic(v___x_2945_);
lean_inc_ref(v___x_2946_);
v___x_2947_ = l_Lean_Parser_many(v___x_2946_);
v___x_2948_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7);
v___x_2949_ = l_Lean_Parser_andthen(v___x_2947_, v___x_2948_);
v___x_2950_ = l_Lean_Parser_andthen(v___x_2942_, v___x_2949_);
v___x_2951_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8);
v___x_2952_ = l_Lean_Parser_many1(v___x_2946_);
v___x_2953_ = l_Lean_Parser_andthen(v___x_2952_, v___x_2951_);
v___x_2954_ = l_Lean_Parser_andthen(v___x_2951_, v___x_2953_);
v___x_2955_ = l_Lean_Parser_orelse(v___x_2950_, v___x_2954_);
v___x_2956_ = l_Lean_Parser_andthen(v___x_2941_, v___x_2955_);
v___x_2957_ = l_Lean_Parser_andthen(v___x_2940_, v___x_2956_);
v___x_2958_ = l_Lean_Parser_andthen(v___x_2939_, v___x_2957_);
v___x_2959_ = l_Lean_Parser_andthen(v___x_2938_, v___x_2958_);
v___x_2960_ = 0;
v___x_2961_ = l_Lean_Parser_nodeWithAntiquot(v___x_2936_, v___x_2937_, v___x_2959_, v___x_2960_);
v_fn_2962_ = lean_ctor_get(v___x_2961_, 1);
lean_inc_ref(v_fn_2962_);
lean_dec_ref(v___x_2961_);
v___x_2963_ = lean_apply_2(v_fn_2962_, v_a_2934_, v_a_2935_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot(lean_object* v_c_2964_, lean_object* v_s_2965_){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; lean_object* v_fn_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v_alts_2992_; lean_object* v_fn_2993_; lean_object* v___x_2994_; 
v___x_2966_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2967_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0);
v___x_2968_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot), 2, 0);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2966_);
lean_ctor_set(v___x_2969_, 1, v___x_2968_);
v___x_2970_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot), 2, 0);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2966_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1);
v___x_2973_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2);
v___x_2974_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot), 2, 0);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2966_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3);
v___x_2977_ = 1;
v___x_2978_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5);
v_fn_2979_ = lean_ctor_get(v___x_2978_, 1);
v___x_2980_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6);
v___x_2981_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
v___x_2982_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot), 2, 0);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2966_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = l_Lean_Parser_orelse(v___x_2980_, v___x_2983_);
v___x_2985_ = l_Lean_Parser_orelse(v___x_2976_, v___x_2984_);
v___x_2986_ = l_Lean_Parser_orelse(v___x_2975_, v___x_2985_);
v___x_2987_ = l_Lean_Parser_orelse(v___x_2973_, v___x_2986_);
v___x_2988_ = l_Lean_Parser_orelse(v___x_2972_, v___x_2987_);
v___x_2989_ = l_Lean_Parser_orelse(v___x_2981_, v___x_2988_);
v___x_2990_ = l_Lean_Parser_orelse(v___x_2971_, v___x_2989_);
v___x_2991_ = l_Lean_Parser_orelse(v___x_2969_, v___x_2990_);
v_alts_2992_ = l_Lean_Parser_orelse(v___x_2967_, v___x_2991_);
v_fn_2993_ = lean_ctor_get(v_alts_2992_, 1);
lean_inc_ref(v_fn_2993_);
lean_dec_ref(v_alts_2992_);
lean_inc_ref(v_fn_2979_);
v___x_2994_ = l_Lean_Parser_withAntiquotFn(v_fn_2979_, v_fn_2993_, v___x_2977_, v_c_2964_, v_s_2965_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot(lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; lean_object* v___x_3009_; lean_object* v_fn_3010_; lean_object* v___x_3011_; 
v___x_2997_ = ((lean_object*)(l_Lean_Doc_Syntax_bold___closed__0));
v___x_2998_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_2999_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3000_ = l_Lean_Doc_Parser_boldDelimiter;
v___x_3001_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_2999_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = l_Lean_Parser_atomic(v___x_3002_);
v___x_3004_ = l_Lean_Parser_many(v___x_3003_);
v___x_3005_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
v___x_3006_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_3006_, 0, v___x_3000_);
lean_closure_set(v___x_3006_, 1, v___x_3005_);
lean_closure_set(v___x_3006_, 2, v___x_3004_);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_2999_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = 0;
v___x_3009_ = l_Lean_Parser_nodeWithAntiquot(v___x_2997_, v___x_2998_, v___x_3007_, v___x_3008_);
v_fn_3010_ = lean_ctor_get(v___x_3009_, 1);
lean_inc_ref(v_fn_3010_);
lean_dec_ref(v___x_3009_);
v___x_3011_ = lean_apply_2(v_fn_3010_, v_a_2995_, v_a_2996_);
return v___x_3011_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text___closed__0(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_3013_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text(void){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_text___closed__0, &l_Lean_Doc_Parser_Inline_text___closed__0_once, _init_l_Lean_Doc_Parser_Inline_text___closed__0);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1(){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_3023_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0));
v___x_3024_ = l_Lean_addBuiltinDocString(v___x_3022_, v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1(){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_3034_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0));
v___x_3035_ = l_Lean_addBuiltinDocString(v___x_3033_, v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object* v_a_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
return v_res_3037_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_code(void){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1(){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1));
v___x_3041_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0));
v___x_3042_ = l_Lean_addBuiltinDocString(v___x_3040_, v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
return v_res_3044_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_inline__math(void){
_start:
{
lean_object* v___x_3045_; 
v___x_3045_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1(){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_3048_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0));
v___x_3049_ = l_Lean_addBuiltinDocString(v___x_3047_, v___x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
return v_res_3051_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_display__math(void){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1(){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_3055_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0));
v___x_3056_ = l_Lean_addBuiltinDocString(v___x_3054_, v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1(){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_3066_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0));
v___x_3067_ = l_Lean_addBuiltinDocString(v___x_3065_, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
return v_res_3069_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image___closed__0(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_3071_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3070_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image(void){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_image___closed__0, &l_Lean_Doc_Parser_Inline_image___closed__0_once, _init_l_Lean_Doc_Parser_Inline_image___closed__0);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1(){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_3076_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0));
v___x_3077_ = l_Lean_addBuiltinDocString(v___x_3075_, v___x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object* v_a_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
return v_res_3079_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote___closed__0(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_3081_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote(void){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_footnote___closed__0, &l_Lean_Doc_Parser_Inline_footnote___closed__0_once, _init_l_Lean_Doc_Parser_Inline_footnote___closed__0);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1(){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_3086_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0));
v___x_3087_ = l_Lean_addBuiltinDocString(v___x_3085_, v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___boxed(lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
return v_res_3089_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_3091_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
return v___x_3092_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak(void){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_linebreak___closed__0, &l_Lean_Doc_Parser_Inline_linebreak___closed__0_once, _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1(){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_3101_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0));
v___x_3102_ = l_Lean_addBuiltinDocString(v___x_3100_, v___x_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object* v_a_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
return v_res_3104_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3117_ = ((lean_object*)(l_Lean_Doc_Parser_inline___closed__1));
v___x_3118_ = l_Lean_Parser_atomic(v___x_3117_);
return v___x_3118_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2);
v___x_3120_ = l_Lean_Parser_many1(v___x_3119_);
return v___x_3120_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4(void){
_start:
{
uint8_t v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3121_ = 0;
v___x_3122_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_3123_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1));
v___x_3124_ = ((lean_object*)(l_Lean_Doc_Syntax_para___closed__0));
v___x_3125_ = l_Lean_Parser_nodeWithAntiquot(v___x_3124_, v___x_3123_, v___x_3122_, v___x_3121_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v___x_3128_; lean_object* v_fn_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4);
v_fn_3129_ = lean_ctor_get(v___x_3128_, 1);
lean_inc_ref(v_fn_3129_);
v___x_3130_ = lean_apply_2(v_fn_3129_, v_a_3126_, v_a_3127_);
return v___x_3130_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_3138_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3139_ = l_Lean_Parser_andthen(v___x_3138_, v___x_3137_);
return v___x_3139_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1);
v___x_3141_ = l_Lean_Parser_ident;
v___x_3142_ = l_Lean_Parser_andthen(v___x_3141_, v___x_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2);
v___x_3144_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1);
v___x_3145_ = l_Lean_Parser_andthen(v___x_3144_, v___x_3143_);
return v___x_3145_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4(void){
_start:
{
uint8_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3146_ = 0;
v___x_3147_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3);
v___x_3148_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_3149_ = ((lean_object*)(l_Lean_Doc_Syntax_command___closed__0));
v___x_3150_ = l_Lean_Parser_nodeWithAntiquot(v___x_3149_, v___x_3148_, v___x_3147_, v___x_3146_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3153_; lean_object* v_fn_3154_; lean_object* v___x_3155_; 
v___x_3153_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4);
v_fn_3154_ = lean_ctor_get(v___x_3153_, 1);
lean_inc_ref(v_fn_3154_);
v___x_3155_ = lean_apply_2(v_fn_3154_, v_a_3151_, v_a_3152_);
return v___x_3155_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__2));
v___x_3163_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1);
v___x_3165_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit;
v___x_3166_ = l_Lean_Parser_andthen(v___x_3165_, v___x_3164_);
return v___x_3166_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2);
v___x_3168_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1);
v___x_3169_ = l_Lean_Parser_andthen(v___x_3168_, v___x_3167_);
return v___x_3169_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4(void){
_start:
{
uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3170_ = 0;
v___x_3171_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3);
v___x_3172_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_3173_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__0));
v___x_3174_ = l_Lean_Parser_nodeWithAntiquot(v___x_3173_, v___x_3172_, v___x_3171_, v___x_3170_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object* v_a_3175_, lean_object* v_a_3176_){
_start:
{
lean_object* v___x_3177_; lean_object* v_fn_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4);
v_fn_3178_ = lean_ctor_get(v___x_3177_, 1);
lean_inc_ref(v_fn_3178_);
v___x_3179_ = lean_apply_2(v_fn_3178_, v_a_3175_, v_a_3176_);
return v___x_3179_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__2));
v___x_3187_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = l_Lean_Doc_Parser_versoLinkRefUrl;
v___x_3189_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1);
v___x_3190_ = l_Lean_Parser_andthen(v___x_3189_, v___x_3188_);
return v___x_3190_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2);
v___x_3192_ = l_Lean_Doc_Parser_versoRef;
v___x_3193_ = l_Lean_Parser_andthen(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3);
v___x_3195_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_3196_ = l_Lean_Parser_andthen(v___x_3195_, v___x_3194_);
return v___x_3196_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5(void){
_start:
{
uint8_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3197_ = 0;
v___x_3198_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4);
v___x_3199_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_3200_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__0));
v___x_3201_ = l_Lean_Parser_nodeWithAntiquot(v___x_3200_, v___x_3199_, v___x_3198_, v___x_3197_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v___x_3204_; lean_object* v_fn_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5);
v_fn_3205_ = lean_ctor_get(v___x_3204_, 1);
lean_inc_ref(v_fn_3205_);
v___x_3206_ = lean_apply_2(v_fn_3205_, v_a_3202_, v_a_3203_);
return v___x_3206_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2);
v___x_3214_ = l_Lean_Parser_many(v___x_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1);
v___x_3216_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1);
v___x_3217_ = l_Lean_Parser_andthen(v___x_3216_, v___x_3215_);
return v___x_3217_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2);
v___x_3219_ = l_Lean_Doc_Parser_versoRef;
v___x_3220_ = l_Lean_Parser_andthen(v___x_3219_, v___x_3218_);
return v___x_3220_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3);
v___x_3222_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1);
v___x_3223_ = l_Lean_Parser_andthen(v___x_3222_, v___x_3221_);
return v___x_3223_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5(void){
_start:
{
uint8_t v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3224_ = 0;
v___x_3225_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4);
v___x_3226_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_3227_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__0));
v___x_3228_ = l_Lean_Parser_nodeWithAntiquot(v___x_3227_, v___x_3226_, v___x_3225_, v___x_3224_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v___x_3231_; lean_object* v_fn_3232_; lean_object* v___x_3233_; 
v___x_3231_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5);
v_fn_3232_ = lean_ctor_get(v___x_3231_, 1);
lean_inc_ref(v_fn_3232_);
v___x_3233_ = lean_apply_2(v_fn_3232_, v_a_3229_, v_a_3230_);
return v___x_3233_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3240_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_3241_ = l_Lean_Doc_Parser_headerMarker;
v___x_3242_ = l_Lean_Parser_andthen(v___x_3241_, v___x_3240_);
return v___x_3242_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2(void){
_start:
{
uint8_t v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3243_ = 0;
v___x_3244_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1);
v___x_3245_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_3246_ = ((lean_object*)(l_Lean_Doc_Syntax_header___closed__0));
v___x_3247_ = l_Lean_Parser_nodeWithAntiquot(v___x_3246_, v___x_3245_, v___x_3244_, v___x_3243_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object* v_a_3248_, lean_object* v_a_3249_){
_start:
{
lean_object* v___x_3250_; lean_object* v_fn_3251_; lean_object* v___x_3252_; 
v___x_3250_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2);
v_fn_3251_ = lean_ctor_get(v___x_3250_, 1);
lean_inc_ref(v_fn_3251_);
v___x_3252_ = lean_apply_2(v_fn_3251_, v_a_3248_, v_a_3249_);
return v___x_3252_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1(void){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3260_ = l_Lean_Parser_ident;
v___x_3261_ = l_Lean_Parser_andthen(v___x_3260_, v___x_3259_);
return v___x_3261_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1);
v___x_3263_ = l_Lean_Parser_optional(v___x_3262_);
return v___x_3263_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = l_Lean_Doc_Parser_codeBlockFence;
v___x_3265_ = l_Lean_Doc_Parser_versoCodeBlock;
v___x_3266_ = l_Lean_Parser_andthen(v___x_3265_, v___x_3264_);
return v___x_3266_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3);
v___x_3268_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2);
v___x_3269_ = l_Lean_Parser_andthen(v___x_3268_, v___x_3267_);
return v___x_3269_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4);
v___x_3271_ = l_Lean_Doc_Parser_codeBlockFence;
v___x_3272_ = l_Lean_Parser_andthen(v___x_3271_, v___x_3270_);
return v___x_3272_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6(void){
_start:
{
uint8_t v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3273_ = 0;
v___x_3274_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5);
v___x_3275_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_3276_ = ((lean_object*)(l_Lean_Doc_Syntax_codeblock___closed__0));
v___x_3277_ = l_Lean_Parser_nodeWithAntiquot(v___x_3276_, v___x_3275_, v___x_3274_, v___x_3273_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object* v_a_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v___x_3280_; lean_object* v_fn_3281_; lean_object* v___x_3282_; 
v___x_3280_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6);
v_fn_3281_ = lean_ctor_get(v___x_3280_, 1);
lean_inc_ref(v_fn_3281_);
v___x_3282_ = lean_apply_2(v_fn_3281_, v_a_3278_, v_a_3279_);
return v___x_3282_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3));
v___x_3302_ = l_Lean_Parser_atomic(v___x_3301_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4);
v___x_3304_ = l_Lean_Parser_many(v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object* v_marker_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; lean_object* v___x_3331_; lean_object* v_fn_3332_; lean_object* v___x_3333_; 
v___x_3322_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0));
v___x_3323_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_3324_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3325_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3324_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = l_Lean_Parser_atomic(v___x_3326_);
v___x_3328_ = l_Lean_Parser_many(v___x_3327_);
v___x_3329_ = l_Lean_Parser_andthen(v_marker_3319_, v___x_3328_);
v___x_3330_ = 0;
v___x_3331_ = l_Lean_Parser_nodeWithAntiquot(v___x_3322_, v___x_3323_, v___x_3329_, v___x_3330_);
v_fn_3332_ = lean_ctor_get(v___x_3331_, 1);
lean_inc_ref(v_fn_3332_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = lean_apply_2(v_fn_3332_, v_a_3320_, v_a_3321_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; lean_object* v_fn_3346_; lean_object* v___x_3347_; 
v___x_3336_ = ((lean_object*)(l_Lean_Doc_Syntax_ul___closed__0));
v___x_3337_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_3338_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3339_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker;
v___x_3340_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3340_, 0, v___x_3339_);
v___x_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3338_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_Parser_atomic(v___x_3341_);
v___x_3343_ = l_Lean_Parser_many1(v___x_3342_);
v___x_3344_ = 0;
v___x_3345_ = l_Lean_Parser_nodeWithAntiquot(v___x_3336_, v___x_3337_, v___x_3343_, v___x_3344_);
v_fn_3346_ = lean_ctor_get(v___x_3345_, 1);
lean_inc_ref(v_fn_3346_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = lean_apply_2(v_fn_3346_, v_a_3334_, v_a_3335_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; lean_object* v___x_3365_; lean_object* v_fn_3366_; lean_object* v___x_3367_; 
v___x_3356_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__0));
v___x_3357_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_3358_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3359_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker;
v___x_3360_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3360_, 0, v___x_3359_);
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3358_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3362_ = l_Lean_Parser_atomic(v___x_3361_);
v___x_3363_ = l_Lean_Parser_many1(v___x_3362_);
v___x_3364_ = 0;
v___x_3365_ = l_Lean_Parser_nodeWithAntiquot(v___x_3356_, v___x_3357_, v___x_3363_, v___x_3364_);
v_fn_3366_ = lean_ctor_get(v___x_3365_, 1);
lean_inc_ref(v_fn_3366_);
lean_dec_ref(v___x_3365_);
v___x_3367_ = lean_apply_2(v_fn_3366_, v_a_3354_, v_a_3355_);
return v___x_3367_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__2));
v___x_3375_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; lean_object* v___x_3388_; lean_object* v_fn_3389_; lean_object* v___x_3390_; 
v___x_3378_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__0));
v___x_3379_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_3380_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1);
v___x_3381_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3382_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = l_Lean_Parser_atomic(v___x_3383_);
v___x_3385_ = l_Lean_Parser_many(v___x_3384_);
v___x_3386_ = l_Lean_Parser_andthen(v___x_3380_, v___x_3385_);
v___x_3387_ = 0;
v___x_3388_ = l_Lean_Parser_nodeWithAntiquot(v___x_3378_, v___x_3379_, v___x_3386_, v___x_3387_);
v_fn_3389_ = lean_ctor_get(v___x_3388_, 1);
lean_inc_ref(v_fn_3389_);
lean_dec_ref(v___x_3388_);
v___x_3390_ = lean_apply_2(v_fn_3389_, v_a_3376_, v_a_3377_);
return v___x_3390_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_3392_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3391_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; lean_object* v_fn_3418_; lean_object* v___x_3419_; 
v___x_3402_ = ((lean_object*)(l_Lean_Doc_Syntax_directive___closed__0));
v___x_3403_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_3404_ = l_Lean_Doc_Parser_directiveDelimiter;
v___x_3405_ = l_Lean_Parser_ident;
v___x_3406_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3407_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3408_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3407_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = l_Lean_Parser_atomic(v___x_3409_);
v___x_3411_ = l_Lean_Parser_many(v___x_3410_);
v___x_3412_ = l_Lean_Parser_andthen(v___x_3411_, v___x_3404_);
v___x_3413_ = l_Lean_Parser_andthen(v___x_3406_, v___x_3412_);
v___x_3414_ = l_Lean_Parser_andthen(v___x_3405_, v___x_3413_);
v___x_3415_ = l_Lean_Parser_andthen(v___x_3404_, v___x_3414_);
v___x_3416_ = 0;
v___x_3417_ = l_Lean_Parser_nodeWithAntiquot(v___x_3402_, v___x_3403_, v___x_3415_, v___x_3416_);
v_fn_3418_ = lean_ctor_get(v___x_3417_, 1);
lean_inc_ref(v_fn_3418_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = lean_apply_2(v_fn_3418_, v_a_3400_, v_a_3401_);
return v___x_3419_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6(void){
_start:
{
uint8_t v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3425_ = 1;
v___x_3426_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5));
v___x_3427_ = ((lean_object*)(l_Lean_Doc_Syntax_block_quot___closed__0));
v___x_3428_ = l_Lean_Parser_mkAntiquot(v___x_3427_, v___x_3426_, v___x_3425_, v___x_3425_);
return v___x_3428_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8(void){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_3430_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set(v___x_3431_, 1, v___x_3429_);
return v___x_3431_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_3433_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3432_);
return v___x_3434_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8);
v___x_3436_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7);
v___x_3437_ = l_Lean_Parser_orelse(v___x_3436_, v___x_3435_);
return v___x_3437_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_3439_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3439_);
lean_ctor_set(v___x_3440_, 1, v___x_3438_);
return v___x_3440_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9);
v___x_3442_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4);
v___x_3443_ = l_Lean_Parser_orelse(v___x_3442_, v___x_3441_);
return v___x_3443_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_3445_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3445_);
lean_ctor_set(v___x_3446_, 1, v___x_3444_);
return v___x_3446_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10);
v___x_3448_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3);
v___x_3449_ = l_Lean_Parser_orelse(v___x_3448_, v___x_3447_);
return v___x_3449_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_3451_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3451_);
lean_ctor_set(v___x_3452_, 1, v___x_3450_);
return v___x_3452_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11);
v___x_3454_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2);
v___x_3455_ = l_Lean_Parser_orelse(v___x_3454_, v___x_3453_);
return v___x_3455_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1(void){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_3457_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
lean_ctor_set(v___x_3458_, 1, v___x_3456_);
return v___x_3458_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13(void){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3459_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12);
v___x_3460_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1);
v___x_3461_ = l_Lean_Parser_orelse(v___x_3460_, v___x_3459_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object* v_c_3462_, lean_object* v_s_3463_){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; uint8_t v___x_3476_; lean_object* v___x_3477_; lean_object* v_fn_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v_alts_3485_; lean_object* v_fn_3486_; lean_object* v___x_3487_; 
v___x_3464_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3465_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot), 2, 0);
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot), 2, 0);
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3464_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot), 2, 0);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3464_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot), 2, 0);
v___x_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3464_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0);
v___x_3474_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot), 2, 0);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3464_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = 1;
v___x_3477_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6);
v_fn_3478_ = lean_ctor_get(v___x_3477_, 1);
v___x_3479_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13);
v___x_3480_ = l_Lean_Parser_orelse(v___x_3475_, v___x_3479_);
v___x_3481_ = l_Lean_Parser_orelse(v___x_3473_, v___x_3480_);
v___x_3482_ = l_Lean_Parser_orelse(v___x_3472_, v___x_3481_);
v___x_3483_ = l_Lean_Parser_orelse(v___x_3470_, v___x_3482_);
v___x_3484_ = l_Lean_Parser_orelse(v___x_3468_, v___x_3483_);
v_alts_3485_ = l_Lean_Parser_orelse(v___x_3466_, v___x_3484_);
v_fn_3486_ = lean_ctor_get(v_alts_3485_, 1);
lean_inc_ref(v_fn_3486_);
lean_dec_ref(v_alts_3485_);
lean_inc_ref(v_fn_3478_);
v___x_3487_ = l_Lean_Parser_withAntiquotFn(v_fn_3478_, v_fn_3486_, v___x_3476_, v_c_3462_, v_s_3463_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; lean_object* v___x_3502_; lean_object* v_fn_3503_; lean_object* v___x_3504_; 
v___x_3490_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0));
v___x_3491_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_3492_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker;
v___x_3493_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3494_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5);
v___x_3495_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3493_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = l_Lean_Parser_atomic(v___x_3496_);
v___x_3498_ = l_Lean_Parser_many(v___x_3497_);
v___x_3499_ = l_Lean_Parser_andthen(v___x_3494_, v___x_3498_);
v___x_3500_ = l_Lean_Parser_andthen(v___x_3492_, v___x_3499_);
v___x_3501_ = 0;
v___x_3502_ = l_Lean_Parser_nodeWithAntiquot(v___x_3490_, v___x_3491_, v___x_3500_, v___x_3501_);
v_fn_3503_ = lean_ctor_get(v___x_3502_, 1);
lean_inc_ref(v_fn_3503_);
lean_dec_ref(v___x_3502_);
v___x_3504_ = lean_apply_2(v_fn_3503_, v_a_3488_, v_a_3489_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; lean_object* v___x_3515_; lean_object* v_fn_3516_; lean_object* v___x_3517_; 
v___x_3507_ = ((lean_object*)(l_Lean_Doc_Syntax_dl___closed__0));
v___x_3508_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_3509_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3510_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot), 2, 0);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = l_Lean_Parser_atomic(v___x_3511_);
v___x_3513_ = l_Lean_Parser_many1(v___x_3512_);
v___x_3514_ = 0;
v___x_3515_ = l_Lean_Parser_nodeWithAntiquot(v___x_3507_, v___x_3508_, v___x_3513_, v___x_3514_);
v_fn_3516_ = lean_ctor_get(v___x_3515_, 1);
lean_inc_ref(v_fn_3516_);
lean_dec_ref(v___x_3515_);
v___x_3517_ = lean_apply_2(v_fn_3516_, v_a_3505_, v_a_3506_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ListItem_item___closed__0(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = l_Lean_Doc_Parser_listMarker;
v___x_3519_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3519_, 0, v___x_3518_);
return v___x_3519_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ListItem_item___closed__1(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = lean_obj_once(&l_Lean_Doc_Parser_ListItem_item___closed__0, &l_Lean_Doc_Parser_ListItem_item___closed__0_once, _init_l_Lean_Doc_Parser_ListItem_item___closed__0);
v___x_3521_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
lean_ctor_set(v___x_3522_, 1, v___x_3520_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ListItem_item(void){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = lean_obj_once(&l_Lean_Doc_Parser_ListItem_item___closed__1, &l_Lean_Doc_Parser_ListItem_item___closed__1_once, _init_l_Lean_Doc_Parser_ListItem_item___closed__1);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1(){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_3526_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0));
v___x_3527_ = l_Lean_addBuiltinDocString(v___x_3525_, v___x_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object* v_a_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1(){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_3537_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0));
v___x_3538_ = l_Lean_addBuiltinDocString(v___x_3536_, v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object* v_a_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
return v_res_3540_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para___closed__0(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_3542_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
lean_ctor_set(v___x_3543_, 1, v___x_3541_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para(void){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_obj_once(&l_Lean_Doc_Parser_Block_para___closed__0, &l_Lean_Doc_Parser_Block_para___closed__0_once, _init_l_Lean_Doc_Parser_Block_para___closed__0);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1(){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3546_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1));
v___x_3547_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0));
v___x_3548_ = l_Lean_addBuiltinDocString(v___x_3546_, v___x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1(){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_3558_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0));
v___x_3559_ = l_Lean_addBuiltinDocString(v___x_3557_, v___x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1(){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_3569_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0));
v___x_3570_ = l_Lean_addBuiltinDocString(v___x_3568_, v___x_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1(){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3579_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_3580_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0));
v___x_3581_ = l_Lean_addBuiltinDocString(v___x_3579_, v___x_3580_);
return v___x_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1(){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_3591_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0));
v___x_3592_ = l_Lean_addBuiltinDocString(v___x_3590_, v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
return v_res_3594_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock___closed__0(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_3596_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v___x_3595_);
return v___x_3597_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock(void){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = lean_obj_once(&l_Lean_Doc_Parser_Block_codeblock___closed__0, &l_Lean_Doc_Parser_Block_codeblock___closed__0_once, _init_l_Lean_Doc_Parser_Block_codeblock___closed__0);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1(){
_start:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_3601_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0));
v___x_3602_ = l_Lean_addBuiltinDocString(v___x_3600_, v___x_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1(){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3611_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_3612_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0));
v___x_3613_ = l_Lean_addBuiltinDocString(v___x_3611_, v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
return v_res_3615_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header___closed__0(void){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3616_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_3617_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v___x_3616_);
return v___x_3618_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header(void){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_obj_once(&l_Lean_Doc_Parser_Block_header___closed__0, &l_Lean_Doc_Parser_Block_header___closed__0_once, _init_l_Lean_Doc_Parser_Block_header___closed__0);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1(){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_3622_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0));
v___x_3623_ = l_Lean_addBuiltinDocString(v___x_3621_, v___x_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object* v_a_3624_){
_start:
{
lean_object* v_res_3625_; 
v_res_3625_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
return v_res_3625_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref___closed__0(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_3627_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
lean_ctor_set(v___x_3628_, 1, v___x_3626_);
return v___x_3628_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref(void){
_start:
{
lean_object* v___x_3629_; 
v___x_3629_ = lean_obj_once(&l_Lean_Doc_Parser_Block_link__ref___closed__0, &l_Lean_Doc_Parser_Block_link__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_link__ref___closed__0);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1(){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_3632_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0));
v___x_3633_ = l_Lean_addBuiltinDocString(v___x_3631_, v___x_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object* v_a_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
return v_res_3635_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3636_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_3637_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
lean_ctor_set(v___x_3638_, 1, v___x_3636_);
return v___x_3638_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref(void){
_start:
{
lean_object* v___x_3639_; 
v___x_3639_ = lean_obj_once(&l_Lean_Doc_Parser_Block_footnote__ref___closed__0, &l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1(){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3641_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_3642_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0));
v___x_3643_ = l_Lean_addBuiltinDocString(v___x_3641_, v___x_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
return v_res_3645_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0(void){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3646_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_3647_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
lean_ctor_set(v___x_3648_, 1, v___x_3646_);
return v___x_3648_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block(void){
_start:
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_obj_once(&l_Lean_Doc_Parser_Block_metadata__block___closed__0, &l_Lean_Doc_Parser_Block_metadata__block___closed__0_once, _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1(){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3651_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_3652_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0));
v___x_3653_ = l_Lean_addBuiltinDocString(v___x_3651_, v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object* v_a_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
return v_res_3655_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command___closed__0(void){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_3657_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
lean_ctor_set(v___x_3658_, 1, v___x_3656_);
return v___x_3658_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command(void){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = lean_obj_once(&l_Lean_Doc_Parser_Block_command___closed__0, &l_Lean_Doc_Parser_Block_command___closed__0_once, _init_l_Lean_Doc_Parser_Block_command___closed__0);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1(){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_3662_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0));
v___x_3663_ = l_Lean_addBuiltinDocString(v___x_3661_, v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object* v_a_3664_){
_start:
{
lean_object* v_res_3665_; 
v_res_3665_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
return v_res_3665_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___closed__2(void){
_start:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = ((lean_object*)(l_Lean_Doc_Parser_block));
v___x_3678_ = l_Lean_Parser_atomic(v___x_3677_);
return v___x_3678_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___closed__3(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_obj_once(&l_Lean_Doc_Parser_document___closed__2, &l_Lean_Doc_Parser_document___closed__2_once, _init_l_Lean_Doc_Parser_document___closed__2);
v___x_3680_ = l_Lean_Parser_many(v___x_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___closed__4(void){
_start:
{
uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3681_ = 0;
v___x_3682_ = lean_obj_once(&l_Lean_Doc_Parser_document___closed__3, &l_Lean_Doc_Parser_document___closed__3_once, _init_l_Lean_Doc_Parser_document___closed__3);
v___x_3683_ = ((lean_object*)(l_Lean_Doc_Parser_document___closed__1));
v___x_3684_ = ((lean_object*)(l_Lean_Doc_Parser_document___closed__0));
v___x_3685_ = l_Lean_Parser_nodeWithAntiquot(v___x_3684_, v___x_3683_, v___x_3682_, v___x_3681_);
return v___x_3685_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document(void){
_start:
{
lean_object* v___x_3686_; 
v___x_3686_ = lean_obj_once(&l_Lean_Doc_Parser_document___closed__4, &l_Lean_Doc_Parser_document___closed__4_once, _init_l_Lean_Doc_Parser_document___closed__4);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(size_t v_sz_3687_, size_t v_i_3688_, lean_object* v_bs_3689_){
_start:
{
uint8_t v___x_3690_; 
v___x_3690_ = lean_usize_dec_lt(v_i_3688_, v_sz_3687_);
if (v___x_3690_ == 0)
{
return v_bs_3689_;
}
else
{
lean_object* v_v_3691_; lean_object* v___x_3692_; lean_object* v_bs_x27_3693_; size_t v___x_3694_; size_t v___x_3695_; lean_object* v___x_3696_; 
v_v_3691_ = lean_array_uget(v_bs_3689_, v_i_3688_);
v___x_3692_ = lean_unsigned_to_nat(0u);
v_bs_x27_3693_ = lean_array_uset(v_bs_3689_, v_i_3688_, v___x_3692_);
v___x_3694_ = ((size_t)1ULL);
v___x_3695_ = lean_usize_add(v_i_3688_, v___x_3694_);
v___x_3696_ = lean_array_uset(v_bs_x27_3693_, v_i_3688_, v_v_3691_);
v_i_3688_ = v___x_3695_;
v_bs_3689_ = v___x_3696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0___boxed(lean_object* v_sz_3698_, lean_object* v_i_3699_, lean_object* v_bs_3700_){
_start:
{
size_t v_sz_boxed_3701_; size_t v_i_boxed_3702_; lean_object* v_res_3703_; 
v_sz_boxed_3701_ = lean_unbox_usize(v_sz_3698_);
lean_dec(v_sz_3698_);
v_i_boxed_3702_ = lean_unbox_usize(v_i_3699_);
lean_dec(v_i_3699_);
v_res_3703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_boxed_3701_, v_i_boxed_3702_, v_bs_3700_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object* v_doc_3704_){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; size_t v_sz_3708_; size_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = l_Lean_Syntax_getArg(v_doc_3704_, v___x_3705_);
v___x_3707_ = l_Lean_Syntax_getArgs(v___x_3706_);
lean_dec(v___x_3706_);
v_sz_3708_ = lean_array_size(v___x_3707_);
v___x_3709_ = ((size_t)0ULL);
v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_3708_, v___x_3709_, v___x_3707_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks___boxed(lean_object* v_doc_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l_Lean_TSyntax_getVersoBlocks(v_doc_3711_);
lean_dec(v_doc_3711_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object* v_delim_3713_){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3714_ = lean_unsigned_to_nat(0u);
v___x_3715_ = l_Lean_Syntax_getArg(v_delim_3713_, v___x_3714_);
v___x_3716_ = l_Lean_Syntax_getAtomVal(v___x_3715_);
lean_dec(v___x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter___boxed(lean_object* v_delim_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_3717_);
lean_dec(v_delim_3717_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(lean_object* v_s_3721_){
_start:
{
lean_inc(v_s_3721_);
return v_s_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed(lean_object* v_s_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(v_s_3722_);
lean_dec(v_s_3722_);
return v_res_3723_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_versoText = _init_l_Lean_Doc_Parser_versoText();
lean_mark_persistent(l_Lean_Doc_Parser_versoText);
l_Lean_Doc_Parser_versoRef = _init_l_Lean_Doc_Parser_versoRef();
lean_mark_persistent(l_Lean_Doc_Parser_versoRef);
l_Lean_Doc_Parser_versoLinkUrl = _init_l_Lean_Doc_Parser_versoLinkUrl();
lean_mark_persistent(l_Lean_Doc_Parser_versoLinkUrl);
l_Lean_Doc_Parser_versoLinkRefUrl = _init_l_Lean_Doc_Parser_versoLinkRefUrl();
lean_mark_persistent(l_Lean_Doc_Parser_versoLinkRefUrl);
l_Lean_Doc_Parser_versoImageAlt = _init_l_Lean_Doc_Parser_versoImageAlt();
lean_mark_persistent(l_Lean_Doc_Parser_versoImageAlt);
l_Lean_Doc_Parser_versoCode = _init_l_Lean_Doc_Parser_versoCode();
lean_mark_persistent(l_Lean_Doc_Parser_versoCode);
l_Lean_Doc_Parser_versoCodeBlock = _init_l_Lean_Doc_Parser_versoCodeBlock();
lean_mark_persistent(l_Lean_Doc_Parser_versoCodeBlock);
l_Lean_Doc_Parser_versoCodeBlockLine = _init_l_Lean_Doc_Parser_versoCodeBlockLine();
lean_mark_persistent(l_Lean_Doc_Parser_versoCodeBlockLine);
l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1 = _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1);
l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1 = _init_l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1);
l_Lean_Doc_Parser_ArgVal_str = _init_l_Lean_Doc_Parser_ArgVal_str();
lean_mark_persistent(l_Lean_Doc_Parser_ArgVal_str);
l_Lean_Doc_Parser_ArgVal_ident = _init_l_Lean_Doc_Parser_ArgVal_ident();
lean_mark_persistent(l_Lean_Doc_Parser_ArgVal_ident);
l_Lean_Doc_Parser_ArgVal_num = _init_l_Lean_Doc_Parser_ArgVal_num();
lean_mark_persistent(l_Lean_Doc_Parser_ArgVal_num);
l_Lean_Doc_Parser_argVal = _init_l_Lean_Doc_Parser_argVal();
lean_mark_persistent(l_Lean_Doc_Parser_argVal);
l_Lean_Doc_Parser_Arg_anon = _init_l_Lean_Doc_Parser_Arg_anon();
lean_mark_persistent(l_Lean_Doc_Parser_Arg_anon);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Arg_named = _init_l_Lean_Doc_Parser_Arg_named();
lean_mark_persistent(l_Lean_Doc_Parser_Arg_named);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Arg_named__no__paren = _init_l_Lean_Doc_Parser_Arg_named__no__paren();
lean_mark_persistent(l_Lean_Doc_Parser_Arg_named__no__paren);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Arg_flag__on = _init_l_Lean_Doc_Parser_Arg_flag__on();
lean_mark_persistent(l_Lean_Doc_Parser_Arg_flag__on);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Arg_flag__off = _init_l_Lean_Doc_Parser_Arg_flag__off();
lean_mark_persistent(l_Lean_Doc_Parser_Arg_flag__off);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_arg = _init_l_Lean_Doc_Parser_arg();
lean_mark_persistent(l_Lean_Doc_Parser_arg);
l_Lean_Doc_Parser_LinkTarget_url = _init_l_Lean_Doc_Parser_LinkTarget_url();
lean_mark_persistent(l_Lean_Doc_Parser_LinkTarget_url);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_LinkTarget_ref = _init_l_Lean_Doc_Parser_LinkTarget_ref();
lean_mark_persistent(l_Lean_Doc_Parser_LinkTarget_ref);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_linkTarget = _init_l_Lean_Doc_Parser_linkTarget();
lean_mark_persistent(l_Lean_Doc_Parser_linkTarget);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit);
l_Lean_Doc_Parser_headerMarker = _init_l_Lean_Doc_Parser_headerMarker();
lean_mark_persistent(l_Lean_Doc_Parser_headerMarker);
l_Lean_Doc_Parser_listMarker = _init_l_Lean_Doc_Parser_listMarker();
lean_mark_persistent(l_Lean_Doc_Parser_listMarker);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker);
l_Lean_Doc_Parser_emphDelimiter = _init_l_Lean_Doc_Parser_emphDelimiter();
lean_mark_persistent(l_Lean_Doc_Parser_emphDelimiter);
l_Lean_Doc_Parser_boldDelimiter = _init_l_Lean_Doc_Parser_boldDelimiter();
lean_mark_persistent(l_Lean_Doc_Parser_boldDelimiter);
l_Lean_Doc_Parser_codeDelimiter = _init_l_Lean_Doc_Parser_codeDelimiter();
lean_mark_persistent(l_Lean_Doc_Parser_codeDelimiter);
l_Lean_Doc_Parser_codeBlockFence = _init_l_Lean_Doc_Parser_codeBlockFence();
lean_mark_persistent(l_Lean_Doc_Parser_codeBlockFence);
l_Lean_Doc_Parser_inlineMathMarker = _init_l_Lean_Doc_Parser_inlineMathMarker();
lean_mark_persistent(l_Lean_Doc_Parser_inlineMathMarker);
l_Lean_Doc_Parser_displayMathMarker = _init_l_Lean_Doc_Parser_displayMathMarker();
lean_mark_persistent(l_Lean_Doc_Parser_displayMathMarker);
l_Lean_Doc_Parser_directiveDelimiter = _init_l_Lean_Doc_Parser_directiveDelimiter();
lean_mark_persistent(l_Lean_Doc_Parser_directiveDelimiter);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1 = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1 = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1 = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1);
l_Lean_Doc_Parser_Inline_text = _init_l_Lean_Doc_Parser_Inline_text();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_text);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_code = _init_l_Lean_Doc_Parser_Inline_code();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_code);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_inline__math = _init_l_Lean_Doc_Parser_Inline_inline__math();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_inline__math);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_display__math = _init_l_Lean_Doc_Parser_Inline_display__math();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_display__math);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_image = _init_l_Lean_Doc_Parser_Inline_image();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_image);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_footnote = _init_l_Lean_Doc_Parser_Inline_footnote();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_footnote);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_linebreak = _init_l_Lean_Doc_Parser_Inline_linebreak();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_linebreak);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_ListItem_item = _init_l_Lean_Doc_Parser_ListItem_item();
lean_mark_persistent(l_Lean_Doc_Parser_ListItem_item);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_para = _init_l_Lean_Doc_Parser_Block_para();
lean_mark_persistent(l_Lean_Doc_Parser_Block_para);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_codeblock = _init_l_Lean_Doc_Parser_Block_codeblock();
lean_mark_persistent(l_Lean_Doc_Parser_Block_codeblock);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_header = _init_l_Lean_Doc_Parser_Block_header();
lean_mark_persistent(l_Lean_Doc_Parser_Block_header);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_link__ref = _init_l_Lean_Doc_Parser_Block_link__ref();
lean_mark_persistent(l_Lean_Doc_Parser_Block_link__ref);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_footnote__ref = _init_l_Lean_Doc_Parser_Block_footnote__ref();
lean_mark_persistent(l_Lean_Doc_Parser_Block_footnote__ref);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_metadata__block = _init_l_Lean_Doc_Parser_Block_metadata__block();
lean_mark_persistent(l_Lean_Doc_Parser_Block_metadata__block);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_command = _init_l_Lean_Doc_Parser_Block_command();
lean_mark_persistent(l_Lean_Doc_Parser_Block_command);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_document = _init_l_Lean_Doc_Parser_document();
lean_mark_persistent(l_Lean_Doc_Parser_document);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Category_arg__val = _init_l_Lean_Parser_Category_arg__val();
lean_mark_persistent(l_Lean_Parser_Category_arg__val);
l_Lean_Parser_Category_doc__arg = _init_l_Lean_Parser_Category_doc__arg();
lean_mark_persistent(l_Lean_Parser_Category_doc__arg);
l_Lean_Parser_Category_link__target = _init_l_Lean_Parser_Category_link__target();
lean_mark_persistent(l_Lean_Parser_Category_link__target);
l_Lean_Parser_Category_inline = _init_l_Lean_Parser_Category_inline();
lean_mark_persistent(l_Lean_Parser_Category_inline);
l_Lean_Parser_Category_block = _init_l_Lean_Parser_Category_block();
lean_mark_persistent(l_Lean_Parser_Category_block);
l_Lean_Parser_Category_list__item = _init_l_Lean_Parser_Category_list__item();
lean_mark_persistent(l_Lean_Parser_Category_list__item);
l_Lean_Parser_Category_desc__item = _init_l_Lean_Parser_Category_desc__item();
lean_mark_persistent(l_Lean_Parser_Category_desc__item);
l_Lean_Doc_Syntax_metadataContents = _init_l_Lean_Doc_Syntax_metadataContents();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif

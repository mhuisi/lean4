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
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Doc_Parser_versoCodeLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "versoCodeLine"};
static const lean_object* l_Lean_Doc_Parser_versoCodeLine___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 193, 253, 137, 135, 225, 29, 137)}};
static const lean_object* l_Lean_Doc_Parser_versoCodeLine___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoCodeLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoCodeLine___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeLine;
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
LEAN_EXPORT const lean_object* l_Lean_Doc_versoTextKind = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoRefKind = (const lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkRefUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoImageAltKind = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeKind = (const lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeLineKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeBlockKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value;
static const lean_string_object l_Lean_Doc_parseFailureKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parseFailure"};
static const lean_object* l_Lean_Doc_parseFailureKind___closed__0 = (const lean_object*)&l_Lean_Doc_parseFailureKind___closed__0_value;
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_parseFailureKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 2, 249, 136, 81, 124, 239, 75)}};
static const lean_object* l_Lean_Doc_parseFailureKind___closed__1 = (const lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_parseFailureKind = (const lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_longestBacktickRun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_longestBacktickRun___closed__0 = (const lean_object*)&l_Lean_Doc_longestBacktickRun___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_escapeVersoImageAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_escapeVersoImageAlt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object*);
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
static lean_object* _init_l_Lean_Doc_Parser_versoCodeLine___closed__2(void){
_start:
{
uint8_t v___x_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1454_ = 0;
v___x_1455_ = 1;
v___x_1456_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeLine___closed__1));
v___x_1457_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeLine___closed__0));
v___x_1458_ = l_Lean_Parser_mkAntiquot(v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeLine(void){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeLine___closed__2, &l_Lean_Doc_Parser_versoCodeLine___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeLine___closed__2);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlock___closed__2(void){
_start:
{
uint8_t v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = 0;
v___x_1467_ = 1;
v___x_1468_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___closed__1));
v___x_1469_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___closed__0));
v___x_1470_ = l_Lean_Parser_mkAntiquot(v___x_1469_, v___x_1468_, v___x_1467_, v___x_1466_);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlock(void){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeBlock___closed__2, &l_Lean_Doc_Parser_versoCodeBlock___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeBlock___closed__2);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v___x_1487_, lean_object* v_str_1488_, lean_object* v_a_1489_, lean_object* v_b_1490_){
_start:
{
uint8_t v_decide_1491_; 
v_decide_1491_ = lean_nat_dec_eq(v_a_1489_, v___x_1487_);
if (v_decide_1491_ == 0)
{
lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1517_; 
v_fst_1492_ = lean_ctor_get(v_b_1490_, 0);
v_snd_1493_ = lean_ctor_get(v_b_1490_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_b_1490_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1495_ = v_b_1490_;
v_isShared_1496_ = v_isSharedCheck_1517_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_inc(v_fst_1492_);
lean_dec(v_b_1490_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1517_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
uint32_t v___x_1497_; lean_object* v___x_1498_; uint32_t v___x_1499_; uint8_t v___x_1500_; 
v___x_1497_ = lean_string_utf8_get_fast(v_str_1488_, v_a_1489_);
v___x_1498_ = lean_string_utf8_next_fast(v_str_1488_, v_a_1489_);
lean_dec(v_a_1489_);
v___x_1499_ = 96;
v___x_1500_ = lean_uint32_dec_eq(v___x_1497_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_object* v_best_1501_; lean_object* v___x_1503_; 
lean_dec(v_snd_1493_);
v_best_1501_ = lean_unsigned_to_nat(0u);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v_best_1501_);
v___x_1503_ = v___x_1495_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_fst_1492_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_best_1501_);
v___x_1503_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
v_a_1489_ = v___x_1498_;
v_b_1490_ = v___x_1503_;
goto _start;
}
}
else
{
lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_add(v_snd_1493_, v___x_1506_);
lean_dec(v_snd_1493_);
v___x_1508_ = lean_nat_dec_lt(v_fst_1492_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1510_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1507_);
v___x_1510_ = v___x_1495_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_fst_1492_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1507_);
v___x_1510_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
v_a_1489_ = v___x_1498_;
v_b_1490_ = v___x_1510_;
goto _start;
}
}
else
{
lean_object* v___x_1514_; 
lean_dec(v_fst_1492_);
lean_inc(v___x_1507_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1507_);
lean_ctor_set(v___x_1495_, 0, v___x_1507_);
v___x_1514_ = v___x_1495_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1507_);
v___x_1514_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
v_a_1489_ = v___x_1498_;
v_b_1490_ = v___x_1514_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_1489_);
return v_b_1490_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v___x_1518_, lean_object* v_str_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1518_, v_str_1519_, v_a_1520_, v_b_1521_);
lean_dec_ref(v_str_1519_);
lean_dec(v___x_1518_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun(lean_object* v_str_1525_){
_start:
{
lean_object* v_best_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_fst_1530_; 
v_best_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = ((lean_object*)(l_Lean_Doc_longestBacktickRun___closed__0));
v___x_1528_ = lean_string_utf8_byte_size(v_str_1525_);
v___x_1529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1528_, v_str_1525_, v_best_1526_, v___x_1527_);
v_fst_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_fst_1530_);
lean_dec_ref(v___x_1529_);
return v_fst_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Doc_longestBacktickRun(v_str_1531_);
lean_dec_ref(v_str_1531_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v_str_1535_, lean_object* v_inst_1536_, lean_object* v_R_1537_, lean_object* v_a_1538_, lean_object* v_b_1539_, lean_object* v_c_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1534_, v_str_1535_, v_a_1538_, v_b_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v_str_1544_, lean_object* v_inst_1545_, lean_object* v_R_1546_, lean_object* v_a_1547_, lean_object* v_b_1548_, lean_object* v_c_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(v___x_1542_, v___x_1543_, v_str_1544_, v_inst_1545_, v_R_1546_, v_a_1547_, v_b_1548_, v_c_1549_);
lean_dec_ref(v_str_1544_);
lean_dec(v___x_1543_);
lean_dec_ref(v___x_1542_);
return v_res_1550_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(lean_object* v_s_1551_, uint8_t v___x_1552_, lean_object* v_a_1553_, uint8_t v_b_1554_){
_start:
{
lean_object* v_str_1555_; lean_object* v_startInclusive_1556_; lean_object* v_endExclusive_1557_; lean_object* v___x_1558_; uint8_t v_decide_1559_; 
v_str_1555_ = lean_ctor_get(v_s_1551_, 0);
v_startInclusive_1556_ = lean_ctor_get(v_s_1551_, 1);
v_endExclusive_1557_ = lean_ctor_get(v_s_1551_, 2);
v___x_1558_ = lean_nat_sub(v_endExclusive_1557_, v_startInclusive_1556_);
v_decide_1559_ = lean_nat_dec_eq(v_a_1553_, v___x_1558_);
lean_dec(v___x_1558_);
if (v_decide_1559_ == 0)
{
lean_object* v___x_1560_; uint32_t v___x_1565_; uint32_t v___x_1566_; uint8_t v___x_1567_; 
v___x_1560_ = lean_nat_add(v_startInclusive_1556_, v_a_1553_);
lean_dec(v_a_1553_);
v___x_1565_ = lean_string_utf8_get_fast(v_str_1555_, v___x_1560_);
v___x_1566_ = 32;
v___x_1567_ = lean_uint32_dec_eq(v___x_1565_, v___x_1566_);
if (v___x_1567_ == 0)
{
if (v___x_1552_ == 0)
{
goto v___jp_1561_;
}
else
{
lean_dec(v___x_1560_);
return v___x_1552_;
}
}
else
{
goto v___jp_1561_;
}
v___jp_1561_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_string_utf8_next_fast(v_str_1555_, v___x_1560_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_nat_sub(v___x_1562_, v_startInclusive_1556_);
v_a_1553_ = v___x_1563_;
v_b_1554_ = v_decide_1559_;
goto _start;
}
}
else
{
lean_dec(v_a_1553_);
return v_b_1554_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg___boxed(lean_object* v_s_1568_, lean_object* v___x_1569_, lean_object* v_a_1570_, lean_object* v_b_1571_){
_start:
{
uint8_t v___x_965__boxed_1572_; uint8_t v_b_boxed_1573_; uint8_t v_res_1574_; lean_object* v_r_1575_; 
v___x_965__boxed_1572_ = lean_unbox(v___x_1569_);
v_b_boxed_1573_ = lean_unbox(v_b_1571_);
v_res_1574_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1568_, v___x_965__boxed_1572_, v_a_1570_, v_b_boxed_1573_);
lean_dec_ref(v_s_1568_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(uint8_t v___x_1576_, lean_object* v_s_1577_){
_start:
{
lean_object* v_searcher_1578_; uint8_t v___x_1579_; uint8_t v___x_1580_; 
v_searcher_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = 0;
v___x_1580_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1577_, v___x_1576_, v_searcher_1578_, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0___boxed(lean_object* v___x_1581_, lean_object* v_s_1582_){
_start:
{
uint8_t v___x_988__boxed_1583_; uint8_t v_res_1584_; lean_object* v_r_1585_; 
v___x_988__boxed_1583_ = lean_unbox(v___x_1581_);
v_res_1584_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_988__boxed_1583_, v_s_1582_);
lean_dec_ref(v_s_1582_);
v_r_1585_ = lean_box(v_res_1584_);
return v_r_1585_;
}
}
static lean_object* _init_l_Lean_Doc_versoCodeBoundarySpaces___closed__1(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_1588_ = lean_string_utf8_byte_size(v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object* v_str_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1590_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_1591_ = lean_string_utf8_byte_size(v_str_1589_);
v___x_1592_ = lean_obj_once(&l_Lean_Doc_versoCodeBoundarySpaces___closed__1, &l_Lean_Doc_versoCodeBoundarySpaces___closed__1_once, _init_l_Lean_Doc_versoCodeBoundarySpaces___closed__1);
v___x_1593_ = lean_nat_dec_le(v___x_1592_, v___x_1591_);
if (v___x_1593_ == 0)
{
lean_dec_ref(v_str_1589_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_string_memcmp(v_str_1589_, v___x_1590_, v___x_1594_, v___x_1594_, v___x_1592_);
if (v___x_1595_ == 0)
{
lean_dec_ref(v_str_1589_);
return v___x_1595_;
}
else
{
if (v___x_1593_ == 0)
{
lean_dec_ref(v_str_1589_);
return v___x_1593_;
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = lean_nat_sub(v___x_1591_, v___x_1592_);
v___x_1597_ = lean_string_memcmp(v_str_1589_, v___x_1590_, v___x_1596_, v___x_1594_, v___x_1592_);
lean_dec(v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v_str_1589_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1598_, 0, v_str_1589_);
lean_ctor_set(v___x_1598_, 1, v___x_1594_);
lean_ctor_set(v___x_1598_, 2, v___x_1591_);
v___x_1599_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_1597_, v___x_1598_);
lean_dec_ref_known(v___x_1598_, 3);
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBoundarySpaces___boxed(lean_object* v_str_1600_){
_start:
{
uint8_t v_res_1601_; lean_object* v_r_1602_; 
v_res_1601_ = l_Lean_Doc_versoCodeBoundarySpaces(v_str_1600_);
v_r_1602_ = lean_box(v_res_1601_);
return v_r_1602_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(lean_object* v_s_1603_, uint8_t v___x_1604_, lean_object* v_inst_1605_, lean_object* v_R_1606_, lean_object* v_a_1607_, uint8_t v_b_1608_, lean_object* v_c_1609_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1603_, v___x_1604_, v_a_1607_, v_b_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___boxed(lean_object* v_s_1611_, lean_object* v___x_1612_, lean_object* v_inst_1613_, lean_object* v_R_1614_, lean_object* v_a_1615_, lean_object* v_b_1616_, lean_object* v_c_1617_){
_start:
{
uint8_t v___x_1024__boxed_1618_; uint8_t v_b_boxed_1619_; uint8_t v_res_1620_; lean_object* v_r_1621_; 
v___x_1024__boxed_1618_ = lean_unbox(v___x_1612_);
v_b_boxed_1619_ = lean_unbox(v_b_1616_);
v_res_1620_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(v_s_1611_, v___x_1024__boxed_1618_, v_inst_1613_, v_R_1614_, v_a_1615_, v_b_boxed_1619_, v_c_1617_);
lean_dec_ref(v_s_1611_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(lean_object* v_str_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v_fst_1624_; lean_object* v_snd_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1652_; 
v_fst_1624_ = lean_ctor_get(v_a_1623_, 0);
v_snd_1625_ = lean_ctor_get(v_a_1623_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_a_1623_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1627_ = v_a_1623_;
v_isShared_1628_ = v_isSharedCheck_1652_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_snd_1625_);
lean_inc(v_fst_1624_);
lean_dec(v_a_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1652_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; uint8_t v_decide_1630_; 
v___x_1629_ = lean_string_utf8_byte_size(v_str_1622_);
v_decide_1630_ = lean_nat_dec_eq(v_snd_1625_, v___x_1629_);
if (v_decide_1630_ == 0)
{
uint32_t v___x_1631_; lean_object* v___x_1632_; uint32_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1631_ = lean_string_utf8_get_fast(v_str_1622_, v_snd_1625_);
v___x_1632_ = lean_string_utf8_next_fast(v_str_1622_, v_snd_1625_);
lean_dec(v_snd_1625_);
v___x_1638_ = 92;
v___x_1639_ = lean_uint32_dec_eq(v___x_1631_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_del_object(v___x_1627_);
v___x_1640_ = lean_string_push(v_fst_1624_, v___x_1631_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v___x_1632_);
v_a_1623_ = v___x_1641_;
goto _start;
}
else
{
uint8_t v_decide_1643_; 
v_decide_1643_ = lean_nat_dec_eq(v___x_1632_, v___x_1629_);
if (v_decide_1643_ == 0)
{
if (v___x_1639_ == 0)
{
goto v___jp_1633_;
}
else
{
uint32_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_del_object(v___x_1627_);
v___x_1644_ = lean_string_utf8_get_fast(v_str_1622_, v___x_1632_);
v___x_1645_ = lean_string_push(v_fst_1624_, v___x_1644_);
v___x_1646_ = lean_string_utf8_next_fast(v_str_1622_, v___x_1632_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v_a_1623_ = v___x_1647_;
goto _start;
}
}
else
{
goto v___jp_1633_;
}
}
v___jp_1633_:
{
lean_object* v___x_1635_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1632_);
v___x_1635_ = v___x_1627_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_fst_1624_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1632_);
v___x_1635_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
v_a_1623_ = v___x_1635_;
goto _start;
}
}
}
else
{
lean_object* v___x_1650_; 
if (v_isShared_1628_ == 0)
{
v___x_1650_ = v___x_1627_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_fst_1624_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_snd_1625_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg___boxed(lean_object* v_str_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1653_, v_a_1654_);
lean_dec_ref(v_str_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(lean_object* v_str_1660_){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v_fst_1663_; 
v___x_1661_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1));
v___x_1662_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1660_, v___x_1661_);
v_fst_1663_ = lean_ctor_get(v___x_1662_, 0);
lean_inc(v_fst_1663_);
lean_dec_ref(v___x_1662_);
return v_fst_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___boxed(lean_object* v_str_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_str_1664_);
lean_dec_ref(v_str_1664_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(lean_object* v_str_1666_, lean_object* v_inst_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1666_, v_a_1668_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___boxed(lean_object* v_str_1670_, lean_object* v_inst_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(v_str_1670_, v_inst_1671_, v_a_1672_);
lean_dec_ref(v_str_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(uint32_t v_a_1674_, lean_object* v_x_1675_){
_start:
{
if (lean_obj_tag(v_x_1675_) == 0)
{
uint8_t v___x_1676_; 
v___x_1676_ = 0;
return v___x_1676_;
}
else
{
lean_object* v_head_1677_; lean_object* v_tail_1678_; uint32_t v___x_1679_; uint8_t v___x_1680_; 
v_head_1677_ = lean_ctor_get(v_x_1675_, 0);
v_tail_1678_ = lean_ctor_get(v_x_1675_, 1);
v___x_1679_ = lean_unbox_uint32(v_head_1677_);
v___x_1680_ = lean_uint32_dec_eq(v_a_1674_, v___x_1679_);
if (v___x_1680_ == 0)
{
v_x_1675_ = v_tail_1678_;
goto _start;
}
else
{
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0___boxed(lean_object* v_a_1682_, lean_object* v_x_1683_){
_start:
{
uint32_t v_a_boxed_1684_; uint8_t v_res_1685_; lean_object* v_r_1686_; 
v_a_boxed_1684_ = lean_unbox_uint32(v_a_1682_);
lean_dec(v_a_1682_);
v_res_1685_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v_a_boxed_1684_, v_x_1683_);
lean_dec(v_x_1683_);
v_r_1686_ = lean_box(v_res_1685_);
return v_r_1686_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(lean_object* v_delimiters_1687_, lean_object* v___x_1688_, lean_object* v_value_1689_, lean_object* v_a_1690_, lean_object* v_b_1691_){
_start:
{
uint8_t v_decide_1692_; 
v_decide_1692_ = lean_nat_dec_eq(v_a_1690_, v___x_1688_);
if (v_decide_1692_ == 0)
{
uint32_t v___x_1693_; lean_object* v___x_1694_; uint32_t v___x_1695_; uint8_t v___x_1700_; 
v___x_1693_ = lean_string_utf8_get_fast(v_value_1689_, v_a_1690_);
v___x_1694_ = lean_string_utf8_next_fast(v_value_1689_, v_a_1690_);
lean_dec(v_a_1690_);
v___x_1695_ = 92;
v___x_1700_ = lean_uint32_dec_eq(v___x_1693_, v___x_1695_);
if (v___x_1700_ == 0)
{
uint8_t v___x_1701_; 
v___x_1701_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v___x_1693_, v_delimiters_1687_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_string_push(v_b_1691_, v___x_1693_);
v_a_1690_ = v___x_1694_;
v_b_1691_ = v___x_1702_;
goto _start;
}
else
{
goto v___jp_1696_;
}
}
else
{
goto v___jp_1696_;
}
v___jp_1696_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_string_push(v_b_1691_, v___x_1695_);
v___x_1698_ = lean_string_push(v___x_1697_, v___x_1693_);
v_a_1690_ = v___x_1694_;
v_b_1691_ = v___x_1698_;
goto _start;
}
}
else
{
lean_dec(v_a_1690_);
return v_b_1691_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg___boxed(lean_object* v_delimiters_1704_, lean_object* v___x_1705_, lean_object* v_value_1706_, lean_object* v_a_1707_, lean_object* v_b_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1704_, v___x_1705_, v_value_1706_, v_a_1707_, v_b_1708_);
lean_dec_ref(v_value_1706_);
lean_dec(v___x_1705_);
lean_dec(v_delimiters_1704_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(lean_object* v_delimiters_1710_, lean_object* v_value_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1713_ = lean_string_utf8_byte_size(v_value_1711_);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1710_, v___x_1713_, v_value_1711_, v___x_1714_, v___x_1712_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited___boxed(lean_object* v_delimiters_1716_, lean_object* v_value_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v_delimiters_1716_, v_value_1717_);
lean_dec_ref(v_value_1717_);
lean_dec(v_delimiters_1716_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(lean_object* v_delimiters_1719_, lean_object* v___x_1720_, lean_object* v___x_1721_, lean_object* v_value_1722_, lean_object* v_inst_1723_, lean_object* v_R_1724_, lean_object* v_a_1725_, lean_object* v_b_1726_, lean_object* v_c_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1719_, v___x_1721_, v_value_1722_, v_a_1725_, v_b_1726_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___boxed(lean_object* v_delimiters_1729_, lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_value_1732_, lean_object* v_inst_1733_, lean_object* v_R_1734_, lean_object* v_a_1735_, lean_object* v_b_1736_, lean_object* v_c_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(v_delimiters_1729_, v___x_1730_, v___x_1731_, v_value_1732_, v_inst_1733_, v_R_1734_, v_a_1735_, v_b_1736_, v_c_1737_);
lean_dec_ref(v_value_1732_);
lean_dec(v___x_1731_);
lean_dec_ref(v___x_1730_);
lean_dec(v_delimiters_1729_);
return v_res_1738_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = 41;
v___x_1740_ = lean_box_uint32(v___x_1739_);
return v___x_1740_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1741_ = lean_box(0);
v___x_1742_ = l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1;
v___x_1743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
lean_ctor_set(v___x_1743_, 1, v___x_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object* v_value_1744_){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_obj_once(&l_Lean_Doc_escapeVersoLinkUrl___closed__0, &l_Lean_Doc_escapeVersoLinkUrl___closed__0_once, _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0);
v___x_1746_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_1745_, v_value_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___boxed(lean_object* v_value_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_1747_);
lean_dec_ref(v_value_1747_);
return v_res_1748_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = 93;
v___x_1750_ = lean_box_uint32(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
v___x_1753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object* v_value_1754_){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_obj_once(&l_Lean_Doc_escapeVersoImageAlt___closed__0, &l_Lean_Doc_escapeVersoImageAlt___closed__0_once, _init_l_Lean_Doc_escapeVersoImageAlt___closed__0);
v___x_1756_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_1755_, v_value_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___boxed(lean_object* v_value_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Doc_escapeVersoImageAlt(v_value_1757_);
lean_dec_ref(v_value_1757_);
return v_res_1758_;
}
}
static lean_object* _init_l_Lean_TSyntax_getVersoText___closed__0(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1760_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText(lean_object* v_s_1761_){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_1763_ = l_Lean_Syntax_isLit_x3f(v___x_1762_, v_s_1761_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1764_;
}
else
{
lean_object* v_val_1765_; lean_object* v___x_1766_; 
v_val_1765_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_val_1765_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1766_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1765_);
lean_dec(v_val_1765_);
return v___x_1766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText___boxed(lean_object* v_s_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_TSyntax_getVersoText(v_s_1767_);
lean_dec(v_s_1767_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object* v_s_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_1771_ = l_Lean_Syntax_isLit_x3f(v___x_1770_, v_s_1769_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1772_; 
v___x_1772_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1772_;
}
else
{
lean_object* v_val_1773_; 
v_val_1773_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v___x_1771_, 1);
return v_val_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource___boxed(lean_object* v_s_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_TSyntax_getVersoTextSource(v_s_1774_);
lean_dec(v_s_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName(lean_object* v_s_1776_){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_Doc_versoRefKind));
v___x_1778_ = l_Lean_Syntax_isLit_x3f(v___x_1777_, v_s_1776_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1779_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1779_;
}
else
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1778_, 1);
return v_val_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName___boxed(lean_object* v_s_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_TSyntax_getVersoRefName(v_s_1781_);
lean_dec(v_s_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object* v_s_1783_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_Lean_Doc_versoLinkUrlKind));
v___x_1785_ = l_Lean_Syntax_isLit_x3f(v___x_1784_, v_s_1783_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1786_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1788_; 
v_val_1787_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1788_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1787_);
lean_dec(v_val_1787_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl___boxed(lean_object* v_s_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_1789_);
lean_dec(v_s_1789_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object* v_s_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Lean_Doc_versoLinkRefUrlKind));
v___x_1793_ = l_Lean_Syntax_isLit_x3f(v___x_1792_, v_s_1791_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1794_;
}
else
{
lean_object* v_val_1795_; 
v_val_1795_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v___x_1793_, 1);
return v_val_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl___boxed(lean_object* v_s_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_1796_);
lean_dec(v_s_1796_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object* v_s_1798_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l_Lean_Doc_versoImageAltKind));
v___x_1800_ = l_Lean_Syntax_isLit_x3f(v___x_1799_, v_s_1798_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1801_;
}
else
{
lean_object* v_val_1802_; lean_object* v___x_1803_; 
v_val_1802_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_val_1802_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1803_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1802_);
lean_dec(v_val_1802_);
return v___x_1803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt___boxed(lean_object* v_s_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_TSyntax_getVersoImageAlt(v_s_1804_);
lean_dec(v_s_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine(lean_object* v_s_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_Doc_versoCodeLineKind));
v___x_1808_ = l_Lean_Syntax_isLit_x3f(v___x_1807_, v_s_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v___x_1809_; 
v___x_1809_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1809_;
}
else
{
lean_object* v_val_1810_; 
v_val_1810_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_val_1810_);
lean_dec_ref_known(v___x_1808_, 1);
return v_val_1810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine___boxed(lean_object* v_s_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_TSyntax_getVersoCodeLine(v_s_1811_);
lean_dec(v_s_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines(lean_object* v_s_1813_){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = l_Lean_Syntax_getArg(v_s_1813_, v___x_1814_);
v___x_1816_ = l_Lean_Syntax_getArgs(v___x_1815_);
lean_dec(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines___boxed(lean_object* v_s_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_TSyntax_getVersoCodeLines(v_s_1817_);
lean_dec(v_s_1817_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(lean_object* v_as_1819_, size_t v_sz_1820_, size_t v_i_1821_, lean_object* v_b_1822_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1821_, v_sz_1820_);
if (v___x_1823_ == 0)
{
return v_b_1822_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; 
v_a_1824_ = lean_array_uget_borrowed(v_as_1819_, v_i_1821_);
v___x_1825_ = l_Lean_TSyntax_getVersoCodeLine(v_a_1824_);
v___x_1826_ = lean_string_append(v_b_1822_, v___x_1825_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_add(v_i_1821_, v___x_1827_);
v_i_1821_ = v___x_1828_;
v_b_1822_ = v___x_1826_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0___boxed(lean_object* v_as_1830_, lean_object* v_sz_1831_, lean_object* v_i_1832_, lean_object* v_b_1833_){
_start:
{
size_t v_sz_boxed_1834_; size_t v_i_boxed_1835_; lean_object* v_res_1836_; 
v_sz_boxed_1834_ = lean_unbox_usize(v_sz_1831_);
lean_dec(v_sz_1831_);
v_i_boxed_1835_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v_as_1830_, v_sz_boxed_1834_, v_i_boxed_1835_, v_b_1833_);
lean_dec_ref(v_as_1830_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object* v_s_1837_){
_start:
{
lean_object* v_str_1838_; lean_object* v___x_1839_; size_t v_sz_1840_; size_t v___x_1841_; lean_object* v___x_1842_; 
v_str_1838_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1839_ = l_Lean_TSyntax_getVersoCodeLines(v_s_1837_);
v_sz_1840_ = lean_array_size(v___x_1839_);
v___x_1841_ = ((size_t)0ULL);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_1839_, v_sz_1840_, v___x_1841_, v_str_1838_);
lean_dec_ref(v___x_1839_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object* v_s_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_TSyntax_getVersoCode(v_s_1843_);
lean_dec(v_s_1843_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object* v_s_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = l_Lean_Syntax_getArg(v_s_1845_, v___x_1846_);
v___x_1848_ = l_Lean_Syntax_getArgs(v___x_1847_);
lean_dec(v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object* v_s_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_1849_);
lean_dec(v_s_1849_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object* v_s_1851_){
_start:
{
lean_object* v_out_1852_; lean_object* v___x_1853_; size_t v_sz_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v_out_1852_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1853_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_1851_);
v_sz_1854_ = lean_array_size(v___x_1853_);
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_1853_, v_sz_1854_, v___x_1855_, v_out_1852_);
lean_dec_ref(v___x_1853_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock___boxed(lean_object* v_s_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_1857_);
lean_dec(v_s_1857_);
return v_res_1858_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_str___closed__3(void){
_start:
{
uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1867_ = 0;
v___x_1868_ = l_Lean_Parser_strLit;
v___x_1869_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___closed__2));
v___x_1870_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___closed__0));
v___x_1871_ = l_Lean_Parser_nodeWithAntiquot(v___x_1870_, v___x_1869_, v___x_1868_, v___x_1867_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_str(void){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_str___closed__3, &l_Lean_Doc_Parser_ArgVal_str___closed__3_once, _init_l_Lean_Doc_Parser_ArgVal_str___closed__3);
return v___x_1872_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_ident___closed__2(void){
_start:
{
uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1880_ = 0;
v___x_1881_ = l_Lean_Parser_ident;
v___x_1882_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___closed__1));
v___x_1883_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___closed__0));
v___x_1884_ = l_Lean_Parser_nodeWithAntiquot(v___x_1883_, v___x_1882_, v___x_1881_, v___x_1880_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_ident(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_ident___closed__2, &l_Lean_Doc_Parser_ArgVal_ident___closed__2_once, _init_l_Lean_Doc_Parser_ArgVal_ident___closed__2);
return v___x_1885_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_num___closed__2(void){
_start:
{
uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1893_ = 0;
v___x_1894_ = l_Lean_Parser_numLit;
v___x_1895_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___closed__1));
v___x_1896_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___closed__0));
v___x_1897_ = l_Lean_Parser_nodeWithAntiquot(v___x_1896_, v___x_1895_, v___x_1894_, v___x_1893_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_num(void){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_num___closed__2, &l_Lean_Doc_Parser_ArgVal_num___closed__2_once, _init_l_Lean_Doc_Parser_ArgVal_num___closed__2);
return v___x_1898_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__2(void){
_start:
{
uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1905_ = 1;
v___x_1906_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___closed__1));
v___x_1907_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___closed__0));
v___x_1908_ = l_Lean_Parser_mkAntiquot(v___x_1907_, v___x_1906_, v___x_1905_, v___x_1905_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__3(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = l_Lean_Doc_Parser_ArgVal_num;
v___x_1910_ = l_Lean_Doc_Parser_ArgVal_ident;
v___x_1911_ = l_Lean_Parser_orelse(v___x_1910_, v___x_1909_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__4(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__3, &l_Lean_Doc_Parser_argVal___closed__3_once, _init_l_Lean_Doc_Parser_argVal___closed__3);
v___x_1913_ = l_Lean_Doc_Parser_ArgVal_str;
v___x_1914_ = l_Lean_Parser_orelse(v___x_1913_, v___x_1912_);
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___closed__5(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__4, &l_Lean_Doc_Parser_argVal___closed__4_once, _init_l_Lean_Doc_Parser_argVal___closed__4);
v___x_1916_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__2, &l_Lean_Doc_Parser_argVal___closed__2_once, _init_l_Lean_Doc_Parser_argVal___closed__2);
v___x_1917_ = l_Lean_Parser_withAntiquot(v___x_1916_, v___x_1915_);
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal(void){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___closed__5, &l_Lean_Doc_Parser_argVal___closed__5_once, _init_l_Lean_Doc_Parser_argVal___closed__5);
return v___x_1918_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_anon___closed__2(void){
_start:
{
uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1926_ = 0;
v___x_1927_ = l_Lean_Doc_Parser_argVal;
v___x_1928_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___closed__1));
v___x_1929_ = ((lean_object*)(l_Lean_Doc_Syntax_anon___closed__0));
v___x_1930_ = l_Lean_Parser_nodeWithAntiquot(v___x_1929_, v___x_1928_, v___x_1927_, v___x_1926_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_anon(void){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_anon___closed__2, &l_Lean_Doc_Parser_Arg_anon___closed__2_once, _init_l_Lean_Doc_Parser_Arg_anon___closed__2);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1(){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___closed__1));
v___x_1934_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0));
v___x_1935_ = l_Lean_addBuiltinDocString(v___x_1933_, v___x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
return v_res_1937_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__1(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__2));
v___x_1945_ = l_Lean_Parser_symbol(v___x_1944_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__2(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__5));
v___x_1947_ = l_Lean_Parser_symbol(v___x_1946_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__3(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = ((lean_object*)(l_Lean_Doc_Syntax_arg__val_quot___closed__13));
v___x_1949_ = l_Lean_Parser_symbol(v___x_1948_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__4(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__3, &l_Lean_Doc_Parser_Arg_named___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___closed__3);
v___x_1951_ = l_Lean_Doc_Parser_argVal;
v___x_1952_ = l_Lean_Parser_andthen(v___x_1951_, v___x_1950_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__5(void){
_start:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1953_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__4, &l_Lean_Doc_Parser_Arg_named___closed__4_once, _init_l_Lean_Doc_Parser_Arg_named___closed__4);
v___x_1954_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__2, &l_Lean_Doc_Parser_Arg_named___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named___closed__2);
v___x_1955_ = l_Lean_Parser_andthen(v___x_1954_, v___x_1953_);
return v___x_1955_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__6(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__5, &l_Lean_Doc_Parser_Arg_named___closed__5_once, _init_l_Lean_Doc_Parser_Arg_named___closed__5);
v___x_1957_ = l_Lean_Parser_ident;
v___x_1958_ = l_Lean_Parser_andthen(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__7(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__6, &l_Lean_Doc_Parser_Arg_named___closed__6_once, _init_l_Lean_Doc_Parser_Arg_named___closed__6);
v___x_1960_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__1, &l_Lean_Doc_Parser_Arg_named___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named___closed__1);
v___x_1961_ = l_Lean_Parser_andthen(v___x_1960_, v___x_1959_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___closed__8(void){
_start:
{
uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1962_ = 0;
v___x_1963_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__7, &l_Lean_Doc_Parser_Arg_named___closed__7_once, _init_l_Lean_Doc_Parser_Arg_named___closed__7);
v___x_1964_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___closed__0));
v___x_1965_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__0));
v___x_1966_ = l_Lean_Parser_nodeWithAntiquot(v___x_1965_, v___x_1964_, v___x_1963_, v___x_1962_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named(void){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__8, &l_Lean_Doc_Parser_Arg_named___closed__8_once, _init_l_Lean_Doc_Parser_Arg_named___closed__8);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1(){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___closed__0));
v___x_1970_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_1971_ = l_Lean_addBuiltinDocString(v___x_1969_, v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object* v_a_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
return v_res_1973_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__1(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = l_Lean_Doc_Parser_argVal;
v___x_1981_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__2, &l_Lean_Doc_Parser_Arg_named___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named___closed__2);
v___x_1982_ = l_Lean_Parser_andthen(v___x_1981_, v___x_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__2(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1983_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___closed__1, &l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__1);
v___x_1984_ = l_Lean_Parser_ident;
v___x_1985_ = l_Lean_Parser_andthen(v___x_1984_, v___x_1983_);
return v___x_1985_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__3(void){
_start:
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1986_ = 0;
v___x_1987_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___closed__2, &l_Lean_Doc_Parser_Arg_named__no__paren___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__2);
v___x_1988_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___closed__0));
v___x_1989_ = ((lean_object*)(l_Lean_Doc_Syntax_named__no__paren___closed__0));
v___x_1990_ = l_Lean_Parser_nodeWithAntiquot(v___x_1989_, v___x_1988_, v___x_1987_, v___x_1986_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren(void){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___closed__3, &l_Lean_Doc_Parser_Arg_named__no__paren___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___closed__3);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1(){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___closed__0));
v___x_1994_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_1995_ = l_Lean_addBuiltinDocString(v___x_1993_, v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
return v_res_1997_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___closed__1(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__2));
v___x_2005_ = l_Lean_Parser_symbol(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___closed__2(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2006_ = l_Lean_Parser_ident;
v___x_2007_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___closed__1, &l_Lean_Doc_Parser_Arg_flag__on___closed__1_once, _init_l_Lean_Doc_Parser_Arg_flag__on___closed__1);
v___x_2008_ = l_Lean_Parser_andthen(v___x_2007_, v___x_2006_);
return v___x_2008_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___closed__3(void){
_start:
{
uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2009_ = 0;
v___x_2010_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___closed__2, &l_Lean_Doc_Parser_Arg_flag__on___closed__2_once, _init_l_Lean_Doc_Parser_Arg_flag__on___closed__2);
v___x_2011_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___closed__0));
v___x_2012_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__0));
v___x_2013_ = l_Lean_Parser_nodeWithAntiquot(v___x_2012_, v___x_2011_, v___x_2010_, v___x_2009_);
return v___x_2013_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on(void){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___closed__3, &l_Lean_Doc_Parser_Arg_flag__on___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__on___closed__3);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1(){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2016_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___closed__0));
v___x_2017_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0));
v___x_2018_ = l_Lean_addBuiltinDocString(v___x_2016_, v___x_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object* v_a_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
return v_res_2020_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___closed__1(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__2));
v___x_2028_ = l_Lean_Parser_symbol(v___x_2027_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___closed__2(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2029_ = l_Lean_Parser_ident;
v___x_2030_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___closed__1, &l_Lean_Doc_Parser_Arg_flag__off___closed__1_once, _init_l_Lean_Doc_Parser_Arg_flag__off___closed__1);
v___x_2031_ = l_Lean_Parser_andthen(v___x_2030_, v___x_2029_);
return v___x_2031_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___closed__3(void){
_start:
{
uint8_t v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2032_ = 0;
v___x_2033_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___closed__2, &l_Lean_Doc_Parser_Arg_flag__off___closed__2_once, _init_l_Lean_Doc_Parser_Arg_flag__off___closed__2);
v___x_2034_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___closed__0));
v___x_2035_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__0));
v___x_2036_ = l_Lean_Parser_nodeWithAntiquot(v___x_2035_, v___x_2034_, v___x_2033_, v___x_2032_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off(void){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___closed__3, &l_Lean_Doc_Parser_Arg_flag__off___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__off___closed__3);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1(){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___closed__0));
v___x_2040_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0));
v___x_2041_ = l_Lean_addBuiltinDocString(v___x_2039_, v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__2(void){
_start:
{
uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2050_ = 1;
v___x_2051_ = ((lean_object*)(l_Lean_Doc_Parser_arg___closed__1));
v___x_2052_ = ((lean_object*)(l_Lean_Doc_Parser_arg___closed__0));
v___x_2053_ = l_Lean_Parser_mkAntiquot(v___x_2052_, v___x_2051_, v___x_2050_, v___x_2050_);
return v___x_2053_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__3(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = l_Lean_Doc_Parser_Arg_named__no__paren;
v___x_2055_ = l_Lean_Parser_atomic(v___x_2054_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__4(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = l_Lean_Doc_Parser_Arg_anon;
v___x_2057_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__3, &l_Lean_Doc_Parser_arg___closed__3_once, _init_l_Lean_Doc_Parser_arg___closed__3);
v___x_2058_ = l_Lean_Parser_orelse(v___x_2057_, v___x_2056_);
return v___x_2058_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__5(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__4, &l_Lean_Doc_Parser_arg___closed__4_once, _init_l_Lean_Doc_Parser_arg___closed__4);
v___x_2060_ = l_Lean_Doc_Parser_Arg_flag__off;
v___x_2061_ = l_Lean_Parser_orelse(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__6(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__5, &l_Lean_Doc_Parser_arg___closed__5_once, _init_l_Lean_Doc_Parser_arg___closed__5);
v___x_2063_ = l_Lean_Doc_Parser_Arg_flag__on;
v___x_2064_ = l_Lean_Parser_orelse(v___x_2063_, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__7(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__6, &l_Lean_Doc_Parser_arg___closed__6_once, _init_l_Lean_Doc_Parser_arg___closed__6);
v___x_2066_ = l_Lean_Doc_Parser_Arg_named;
v___x_2067_ = l_Lean_Parser_orelse(v___x_2066_, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___closed__8(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__7, &l_Lean_Doc_Parser_arg___closed__7_once, _init_l_Lean_Doc_Parser_arg___closed__7);
v___x_2069_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__2, &l_Lean_Doc_Parser_arg___closed__2_once, _init_l_Lean_Doc_Parser_arg___closed__2);
v___x_2070_ = l_Lean_Parser_withAntiquot(v___x_2069_, v___x_2068_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg(void){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_obj_once(&l_Lean_Doc_Parser_arg___closed__8, &l_Lean_Doc_Parser_arg___closed__8_once, _init_l_Lean_Doc_Parser_arg___closed__8);
return v___x_2071_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___closed__2(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__3, &l_Lean_Doc_Parser_Arg_named___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___closed__3);
v___x_2080_ = l_Lean_Doc_Parser_versoLinkUrl;
v___x_2081_ = l_Lean_Parser_andthen(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___closed__3(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___closed__2, &l_Lean_Doc_Parser_LinkTarget_url___closed__2_once, _init_l_Lean_Doc_Parser_LinkTarget_url___closed__2);
v___x_2083_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___closed__1, &l_Lean_Doc_Parser_Arg_named___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named___closed__1);
v___x_2084_ = l_Lean_Parser_andthen(v___x_2083_, v___x_2082_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___closed__4(void){
_start:
{
uint8_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2085_ = 0;
v___x_2086_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___closed__3, &l_Lean_Doc_Parser_LinkTarget_url___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_url___closed__3);
v___x_2087_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___closed__1));
v___x_2088_ = ((lean_object*)(l_Lean_Doc_Syntax_url___closed__0));
v___x_2089_ = l_Lean_Parser_nodeWithAntiquot(v___x_2088_, v___x_2087_, v___x_2086_, v___x_2085_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url(void){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___closed__4, &l_Lean_Doc_Parser_LinkTarget_url___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_url___closed__4);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1(){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___closed__1));
v___x_2093_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0));
v___x_2094_ = l_Lean_addBuiltinDocString(v___x_2092_, v___x_2093_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
return v_res_2096_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__1(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__2));
v___x_2104_ = l_Lean_Parser_symbol(v___x_2103_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__2(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__5));
v___x_2106_ = l_Lean_Parser_symbol(v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__3(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__2, &l_Lean_Doc_Parser_LinkTarget_ref___closed__2_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__2);
v___x_2108_ = l_Lean_Doc_Parser_versoRef;
v___x_2109_ = l_Lean_Parser_andthen(v___x_2108_, v___x_2107_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__4(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2110_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__3, &l_Lean_Doc_Parser_LinkTarget_ref___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__3);
v___x_2111_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__1, &l_Lean_Doc_Parser_LinkTarget_ref___closed__1_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__1);
v___x_2112_ = l_Lean_Parser_andthen(v___x_2111_, v___x_2110_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__5(void){
_start:
{
uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2113_ = 0;
v___x_2114_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__4, &l_Lean_Doc_Parser_LinkTarget_ref___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__4);
v___x_2115_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___closed__0));
v___x_2116_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__0));
v___x_2117_ = l_Lean_Parser_nodeWithAntiquot(v___x_2116_, v___x_2115_, v___x_2114_, v___x_2113_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref(void){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___closed__5, &l_Lean_Doc_Parser_LinkTarget_ref___closed__5_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___closed__5);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1(){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___closed__0));
v___x_2121_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0));
v___x_2122_ = l_Lean_addBuiltinDocString(v___x_2120_, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
return v_res_2124_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___closed__2(void){
_start:
{
uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2131_ = 1;
v___x_2132_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___closed__1));
v___x_2133_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___closed__0));
v___x_2134_ = l_Lean_Parser_mkAntiquot(v___x_2133_, v___x_2132_, v___x_2131_, v___x_2131_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___closed__3(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = l_Lean_Doc_Parser_LinkTarget_ref;
v___x_2136_ = l_Lean_Doc_Parser_LinkTarget_url;
v___x_2137_ = l_Lean_Parser_orelse(v___x_2136_, v___x_2135_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___closed__4(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___closed__3, &l_Lean_Doc_Parser_linkTarget___closed__3_once, _init_l_Lean_Doc_Parser_linkTarget___closed__3);
v___x_2139_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___closed__2, &l_Lean_Doc_Parser_linkTarget___closed__2_once, _init_l_Lean_Doc_Parser_linkTarget___closed__2);
v___x_2140_ = l_Lean_Parser_withAntiquot(v___x_2139_, v___x_2138_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget(void){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___closed__4, &l_Lean_Doc_Parser_linkTarget___closed__4_once, _init_l_Lean_Doc_Parser_linkTarget___closed__4);
return v___x_2141_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
if (lean_obj_tag(v_x_2142_) == 0)
{
if (lean_obj_tag(v_x_2143_) == 0)
{
uint8_t v___x_2144_; 
v___x_2144_ = 1;
return v___x_2144_;
}
else
{
uint8_t v___x_2145_; 
v___x_2145_ = 0;
return v___x_2145_;
}
}
else
{
if (lean_obj_tag(v_x_2143_) == 0)
{
uint8_t v___x_2146_; 
v___x_2146_ = 0;
return v___x_2146_;
}
else
{
lean_object* v_val_2147_; lean_object* v_val_2148_; uint8_t v___x_2149_; 
v_val_2147_ = lean_ctor_get(v_x_2142_, 0);
v_val_2148_ = lean_ctor_get(v_x_2143_, 0);
v___x_2149_ = l_Lean_Parser_instBEqError_beq(v_val_2147_, v_val_2148_);
return v___x_2149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
uint8_t v_res_2152_; lean_object* v_r_2153_; 
v_res_2152_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_x_2150_, v_x_2151_);
lean_dec(v_x_2151_);
lean_dec(v_x_2150_);
v_r_2153_ = lean_box(v_res_2152_);
return v_r_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object* v_x_2154_, lean_object* v_st_2155_){
_start:
{
lean_inc_ref(v_st_2155_);
return v_st_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object* v_x_2156_, lean_object* v_st_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(v_x_2156_, v_st_2157_);
lean_dec_ref(v_st_2157_);
lean_dec_ref(v_x_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2(lean_object* v_x_2159_, lean_object* v___f_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Parser_andthenFn(v_x_2159_, v___f_2160_, v___y_2161_, v___y_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT uint8_t l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(uint32_t v_head_2164_, uint32_t v_x_2165_){
_start:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_uint32_dec_eq(v_x_2165_, v_head_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed(lean_object* v_head_2167_, lean_object* v_x_2168_){
_start:
{
uint32_t v_head_310__boxed_2169_; uint32_t v_x_311__boxed_2170_; uint8_t v_res_2171_; lean_object* v_r_2172_; 
v_head_310__boxed_2169_ = lean_unbox_uint32(v_head_2167_);
lean_dec(v_head_2167_);
v_x_311__boxed_2170_ = lean_unbox_uint32(v_x_2168_);
lean_dec(v_x_2168_);
v_res_2171_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(v_head_310__boxed_2169_, v_x_311__boxed_2170_);
v_r_2172_ = lean_box(v_res_2171_);
return v_r_2172_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(uint32_t v_head_2173_, lean_object* v___f_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2178_ = lean_string_push(v___x_2177_, v_head_2173_);
v___x_2179_ = l_Lean_Parser_satisfyFn(v___f_2174_, v___x_2178_, v___y_2175_, v___y_2176_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed(lean_object* v_head_2180_, lean_object* v___f_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint32_t v_head_319__boxed_2184_; lean_object* v_res_2185_; 
v_head_319__boxed_2184_ = lean_unbox_uint32(v_head_2180_);
lean_dec(v_head_2180_);
v_res_2185_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(v_head_319__boxed_2184_, v___f_2181_, v___y_2182_, v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_apply_2(v_x_2186_, v___y_2188_, v___y_2189_);
return v___x_2190_;
}
else
{
lean_object* v_head_2191_; lean_object* v_tail_2192_; lean_object* v___f_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; 
v_head_2191_ = lean_ctor_get(v_x_2187_, 0);
lean_inc_n(v_head_2191_, 2);
v_tail_2192_ = lean_ctor_get(v_x_2187_, 1);
lean_inc(v_tail_2192_);
lean_dec_ref_known(v_x_2187_, 2);
v___f_2193_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2193_, 0, v_head_2191_);
v___f_2194_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2194_, 0, v_head_2191_);
lean_closure_set(v___f_2194_, 1, v___f_2193_);
v___f_2195_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2), 4, 2);
lean_closure_set(v___f_2195_, 0, v_x_2186_);
lean_closure_set(v___f_2195_, 1, v___f_2194_);
v_x_2186_ = v___f_2195_;
v_x_2187_ = v_tail_2192_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object* v_s_2198_, lean_object* v___f_2199_, lean_object* v_c_2200_, lean_object* v_st_2201_){
_start:
{
lean_object* v___x_2202_; lean_object* v_st_x27_2203_; lean_object* v_errorMsg_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
lean_inc_ref(v_s_2198_);
v___x_2202_ = lean_string_data(v_s_2198_);
lean_inc_ref(v_st_2201_);
v_st_x27_2203_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(v___f_2199_, v___x_2202_, v_c_2200_, v_st_2201_);
v_errorMsg_2204_ = lean_ctor_get(v_st_x27_2203_, 4);
lean_inc(v_errorMsg_2204_);
v___x_2205_ = lean_box(0);
v___x_2206_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2204_, v___x_2205_);
lean_dec(v_errorMsg_2204_);
if (v___x_2206_ == 0)
{
lean_object* v_pos_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_pos_2207_ = lean_ctor_get(v_st_2201_, 2);
lean_inc(v_pos_2207_);
lean_dec_ref(v_st_2201_);
v___x_2208_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2209_ = lean_string_append(v___x_2208_, v_s_2198_);
lean_dec_ref(v_s_2198_);
v___x_2210_ = lean_string_append(v___x_2209_, v___x_2208_);
v___x_2211_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_2203_, v___x_2210_, v_pos_2207_, v___x_2205_);
return v___x_2211_;
}
else
{
lean_dec_ref(v_st_2201_);
lean_dec_ref(v_s_2198_);
return v_st_x27_2203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2(lean_object* v___y_2212_){
_start:
{
lean_inc(v___y_2212_);
return v___y_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2___boxed(lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__2(v___y_2213_);
lean_dec(v___y_2213_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3(lean_object* v___y_2215_){
_start:
{
lean_inc_ref(v___y_2215_);
return v___y_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3___boxed(lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__3(v___y_2216_);
lean_dec_ref(v___y_2216_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object* v_s_2225_){
_start:
{
lean_object* v___f_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___f_2226_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0));
v___f_2227_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1), 4, 2);
lean_closure_set(v___f_2227_, 0, v_s_2225_);
lean_closure_set(v___f_2227_, 1, v___f_2226_);
v___x_2228_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2229_ = 1;
v___x_2230_ = lean_box(v___x_2229_);
v___x_2231_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_2231_, 0, v___f_2227_);
lean_closure_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2228_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_Parser_tokenWithAntiquot(v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(uint32_t v_ch_2234_, uint32_t v_x_2235_){
_start:
{
uint8_t v___x_2236_; 
v___x_2236_ = lean_uint32_dec_eq(v_x_2235_, v_ch_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed(lean_object* v_ch_2237_, lean_object* v_x_2238_){
_start:
{
uint32_t v_ch_boxed_2239_; uint32_t v_x_149__boxed_2240_; uint8_t v_res_2241_; lean_object* v_r_2242_; 
v_ch_boxed_2239_ = lean_unbox_uint32(v_ch_2237_);
lean_dec(v_ch_2237_);
v_x_149__boxed_2240_ = lean_unbox_uint32(v_x_2238_);
lean_dec(v_x_2238_);
v_res_2241_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(v_ch_boxed_2239_, v_x_149__boxed_2240_);
v_r_2242_ = lean_box(v_res_2241_);
return v_r_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(uint32_t v_ch_2244_, lean_object* v___f_2245_, lean_object* v_c_2246_, lean_object* v_st_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v_st_x27_2253_; lean_object* v_errorMsg_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v___x_2248_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2249_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2250_ = lean_string_push(v___x_2249_, v_ch_2244_);
v___x_2251_ = lean_string_append(v___x_2248_, v___x_2250_);
v___x_2252_ = lean_string_append(v___x_2251_, v___x_2248_);
lean_inc_ref(v_st_2247_);
v_st_x27_2253_ = l_Lean_Parser_takeWhile1Fn(v___f_2245_, v___x_2252_, v_c_2246_, v_st_2247_);
v_errorMsg_2254_ = lean_ctor_get(v_st_x27_2253_, 4);
lean_inc(v_errorMsg_2254_);
v___x_2255_ = lean_box(0);
v___x_2256_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2254_, v___x_2255_);
lean_dec(v_errorMsg_2254_);
if (v___x_2256_ == 0)
{
lean_object* v_pos_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_pos_2257_ = lean_ctor_get(v_st_2247_, 2);
lean_inc(v_pos_2257_);
lean_dec_ref(v_st_2247_);
v___x_2258_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0));
v___x_2259_ = lean_string_append(v___x_2258_, v___x_2250_);
lean_dec_ref(v___x_2250_);
v___x_2260_ = lean_string_append(v___x_2259_, v___x_2248_);
v___x_2261_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_2253_, v___x_2260_, v_pos_2257_, v___x_2255_);
return v___x_2261_;
}
else
{
lean_dec_ref(v___x_2250_);
lean_dec_ref(v_st_2247_);
return v_st_x27_2253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed(lean_object* v_ch_2262_, lean_object* v___f_2263_, lean_object* v_c_2264_, lean_object* v_st_2265_){
_start:
{
uint32_t v_ch_boxed_2266_; lean_object* v_res_2267_; 
v_ch_boxed_2266_ = lean_unbox_uint32(v_ch_2262_);
lean_dec(v_ch_2262_);
v_res_2267_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(v_ch_boxed_2266_, v___f_2263_, v_c_2264_, v_st_2265_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(uint32_t v_ch_2268_){
_start:
{
lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2269_ = lean_box_uint32(v_ch_2268_);
v___f_2270_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2270_, 0, v___x_2269_);
v___x_2271_ = lean_box_uint32(v_ch_2268_);
v___f_2272_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2272_, 0, v___x_2271_);
lean_closure_set(v___f_2272_, 1, v___f_2270_);
v___x_2273_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2274_ = 1;
v___x_2275_ = lean_box(v___x_2274_);
v___x_2276_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_2276_, 0, v___f_2272_);
lean_closure_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2273_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_Parser_tokenWithAntiquot(v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___boxed(lean_object* v_ch_2279_){
_start:
{
uint32_t v_ch_boxed_2280_; lean_object* v_res_2281_; 
v_ch_boxed_2280_ = lean_unbox_uint32(v_ch_2279_);
lean_dec(v_ch_2279_);
v_res_2281_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v_ch_boxed_2280_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(lean_object* v_c_2283_, lean_object* v_s_2284_){
_start:
{
lean_object* v_toInputContext_2285_; lean_object* v_pos_2286_; uint8_t v___x_2287_; 
v_toInputContext_2285_ = lean_ctor_get(v_c_2283_, 0);
v_pos_2286_ = lean_ctor_get(v_s_2284_, 2);
v___x_2287_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2285_, v_pos_2286_);
if (v___x_2287_ == 0)
{
lean_object* v_inputString_2288_; uint32_t v_ch_2289_; uint32_t v___x_2290_; uint8_t v___x_2291_; 
lean_inc(v_pos_2286_);
v_inputString_2288_ = lean_ctor_get(v_toInputContext_2285_, 0);
v_ch_2289_ = lean_string_utf8_get_fast(v_inputString_2288_, v_pos_2286_);
v___x_2290_ = 42;
v___x_2291_ = lean_uint32_dec_eq(v_ch_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
uint32_t v___x_2292_; uint8_t v___x_2293_; 
v___x_2292_ = 45;
v___x_2293_ = lean_uint32_dec_eq(v_ch_2289_, v___x_2292_);
if (v___x_2293_ == 0)
{
uint32_t v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = 43;
v___x_2295_ = lean_uint32_dec_eq(v_ch_2289_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0));
v___x_2297_ = lean_box(0);
v___x_2298_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2284_, v___x_2296_, v_pos_2286_, v___x_2297_);
return v___x_2298_;
}
else
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2284_, v_c_2283_, v_pos_2286_);
lean_dec(v_pos_2286_);
return v___x_2299_;
}
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2284_, v_c_2283_, v_pos_2286_);
lean_dec(v_pos_2286_);
return v___x_2300_;
}
}
else
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2284_, v_c_2283_, v_pos_2286_);
lean_dec(v_pos_2286_);
return v___x_2301_;
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_box(0);
v___x_2303_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2284_, v___x_2302_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed(lean_object* v_c_2304_, lean_object* v_s_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(v_c_2304_, v_s_2305_);
lean_dec_ref(v_c_2304_);
return v_res_2306_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2));
v___x_2316_ = l_Lean_Parser_tokenWithAntiquot(v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom(void){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__3);
return v___x_2317_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(uint32_t v_x_2318_){
_start:
{
uint32_t v___x_2319_; uint8_t v___x_2320_; 
v___x_2319_ = 48;
v___x_2320_ = lean_uint32_dec_le(v___x_2319_, v_x_2318_);
if (v___x_2320_ == 0)
{
return v___x_2320_;
}
else
{
uint32_t v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = 57;
v___x_2322_ = lean_uint32_dec_le(v_x_2318_, v___x_2321_);
return v___x_2322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed(lean_object* v_x_2323_){
_start:
{
uint32_t v_x_229__boxed_2324_; uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_x_229__boxed_2324_ = lean_unbox_uint32(v_x_2323_);
lean_dec(v_x_2323_);
v_res_2325_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(v_x_229__boxed_2324_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(uint32_t v_c_2327_){
_start:
{
uint32_t v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = 46;
v___x_2329_ = lean_uint32_dec_eq(v_c_2327_, v___x_2328_);
if (v___x_2329_ == 0)
{
uint32_t v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = 41;
v___x_2331_ = lean_uint32_dec_eq(v_c_2327_, v___x_2330_);
return v___x_2331_;
}
else
{
return v___x_2329_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed(lean_object* v_c_2332_){
_start:
{
uint32_t v_c_boxed_2333_; uint8_t v_res_2334_; lean_object* v_r_2335_; 
v_c_boxed_2333_ = lean_unbox_uint32(v_c_2332_);
lean_dec(v_c_2332_);
v_res_2334_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(v_c_boxed_2333_);
v_r_2335_ = lean_box(v_res_2334_);
return v_r_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(lean_object* v___f_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0));
v___x_2341_ = l_Lean_Parser_satisfyFn(v___f_2337_, v___x_2340_, v___y_2338_, v___y_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed(lean_object* v___f_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(v___f_2342_, v___y_2343_, v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3(lean_object* v___f_2348_, lean_object* v___f_2349_, lean_object* v_c_2350_, lean_object* v_s_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_s_x27_2354_; lean_object* v_errorMsg_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2352_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0));
v___x_2353_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhile1Fn), 4, 2);
lean_closure_set(v___x_2353_, 0, v___f_2348_);
lean_closure_set(v___x_2353_, 1, v___x_2352_);
lean_inc_ref(v_s_2351_);
v_s_x27_2354_ = l_Lean_Parser_andthenFn(v___x_2353_, v___f_2349_, v_c_2350_, v_s_2351_);
v_errorMsg_2355_ = lean_ctor_get(v_s_x27_2354_, 4);
lean_inc(v_errorMsg_2355_);
v___x_2356_ = lean_box(0);
v___x_2357_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2355_, v___x_2356_);
lean_dec(v_errorMsg_2355_);
if (v___x_2357_ == 0)
{
lean_object* v_pos_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_pos_2358_ = lean_ctor_get(v_s_2351_, 2);
lean_inc(v_pos_2358_);
lean_dec_ref(v_s_2351_);
v___x_2359_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1));
v___x_2360_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_x27_2354_, v___x_2359_, v_pos_2358_, v___x_2356_);
return v___x_2360_;
}
else
{
lean_dec_ref(v_s_2351_);
return v_s_x27_2354_;
}
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5));
v___x_2376_ = l_Lean_Parser_tokenWithAntiquot(v___x_2375_);
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom(void){
_start:
{
lean_object* v___x_2377_; 
v___x_2377_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__6);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object* v_c_2378_){
_start:
{
lean_object* v_toInputContext_2379_; lean_object* v_toParserModuleContext_2380_; lean_object* v_toCacheableParserContext_2381_; lean_object* v_tokens_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2391_; 
v_toInputContext_2379_ = lean_ctor_get(v_c_2378_, 0);
v_toParserModuleContext_2380_ = lean_ctor_get(v_c_2378_, 1);
v_toCacheableParserContext_2381_ = lean_ctor_get(v_c_2378_, 2);
v_tokens_2382_ = lean_ctor_get(v_c_2378_, 3);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_c_2378_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2384_ = v_c_2378_;
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_tokens_2382_);
lean_inc(v_toCacheableParserContext_2381_);
lean_inc(v_toParserModuleContext_2380_);
lean_inc(v_toInputContext_2379_);
lean_dec(v_c_2378_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2386_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__2));
v___x_2387_ = l_Lean_Data_Trie_insert___redArg(v_tokens_2382_, v___x_2386_, v___x_2386_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 3, v___x_2387_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_toInputContext_2379_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v_toParserModuleContext_2380_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v_toCacheableParserContext_2381_);
lean_ctor_set(v_reuseFailAlloc_2390_, 3, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2(void){
_start:
{
uint8_t v___x_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2398_ = 0;
v___x_2399_ = 1;
v___x_2400_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1));
v___x_2401_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__4));
v___x_2402_ = l_Lean_Parser_mkAntiquot(v___x_2401_, v___x_2400_, v___x_2399_, v___x_2398_);
return v___x_2402_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__17, &l_Lean_Doc_Syntax_metadataContents___closed__17_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__17);
v___x_2404_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2);
v___x_2405_ = l_Lean_Parser_withAntiquot(v___x_2404_, v___x_2403_);
return v___x_2405_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit(void){
_start:
{
lean_object* v___x_2407_; lean_object* v_fn_2408_; lean_object* v___f_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2407_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__3);
v_fn_2408_ = lean_ctor_get(v___x_2407_, 1);
v___f_2409_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__4));
v___x_2410_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
lean_inc_ref(v_fn_2408_);
v___x_2411_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn), 4, 2);
lean_closure_set(v___x_2411_, 0, v___f_2409_);
lean_closure_set(v___x_2411_, 1, v_fn_2408_);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___closed__2(void){
_start:
{
uint32_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = 35;
v___x_2420_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___closed__3(void){
_start:
{
uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2421_ = 0;
v___x_2422_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___closed__2, &l_Lean_Doc_Parser_headerMarker___closed__2_once, _init_l_Lean_Doc_Parser_headerMarker___closed__2);
v___x_2423_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___closed__1));
v___x_2424_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___closed__0));
v___x_2425_ = l_Lean_Parser_nodeWithAntiquot(v___x_2424_, v___x_2423_, v___x_2422_, v___x_2421_);
return v___x_2425_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker(void){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___closed__3, &l_Lean_Doc_Parser_headerMarker___closed__3_once, _init_l_Lean_Doc_Parser_headerMarker___closed__3);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___closed__2(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom;
v___x_2434_ = l_Lean_Parser_atomic(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___closed__3(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom;
v___x_2436_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___closed__2, &l_Lean_Doc_Parser_listMarker___closed__2_once, _init_l_Lean_Doc_Parser_listMarker___closed__2);
v___x_2437_ = l_Lean_Parser_orelse(v___x_2436_, v___x_2435_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___closed__4(void){
_start:
{
uint8_t v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2438_ = 0;
v___x_2439_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___closed__3, &l_Lean_Doc_Parser_listMarker___closed__3_once, _init_l_Lean_Doc_Parser_listMarker___closed__3);
v___x_2440_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__1));
v___x_2441_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__0));
v___x_2442_ = l_Lean_Parser_nodeWithAntiquot(v___x_2441_, v___x_2440_, v___x_2439_, v___x_2438_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker(void){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___closed__4, &l_Lean_Doc_Parser_listMarker___closed__4_once, _init_l_Lean_Doc_Parser_listMarker___closed__4);
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0(void){
_start:
{
uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2444_ = 0;
v___x_2445_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom;
v___x_2446_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__1));
v___x_2447_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__0));
v___x_2448_ = l_Lean_Parser_nodeWithAntiquot(v___x_2447_, v___x_2446_, v___x_2445_, v___x_2444_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker(void){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0(void){
_start:
{
uint8_t v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2450_ = 0;
v___x_2451_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom;
v___x_2452_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__1));
v___x_2453_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___closed__0));
v___x_2454_ = l_Lean_Parser_nodeWithAntiquot(v___x_2453_, v___x_2452_, v___x_2451_, v___x_2450_);
return v___x_2454_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker(void){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0);
return v___x_2455_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(uint32_t v_x_2456_){
_start:
{
uint32_t v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = 58;
v___x_2458_ = lean_uint32_dec_eq(v_x_2456_, v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed(lean_object* v_x_2459_){
_start:
{
uint32_t v_x_81__boxed_2460_; uint8_t v_res_2461_; lean_object* v_r_2462_; 
v_x_81__boxed_2460_ = lean_unbox_uint32(v_x_2459_);
lean_dec(v_x_2459_);
v_res_2461_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(v_x_81__boxed_2460_);
v_r_2462_ = lean_box(v_res_2461_);
return v_r_2462_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Lean_Doc_Syntax_desc___closed__2));
v___x_2465_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2));
v___x_2474_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__4));
v___x_2475_ = l_Lean_Parser_notFollowedBy(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__5);
v___x_2477_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1);
v___x_2478_ = l_Lean_Parser_andthen(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__6);
v___x_2480_ = l_Lean_Parser_atomic(v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker(void){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__7);
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = 95;
v___x_2489_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2490_ = 0;
v___x_2491_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___closed__2, &l_Lean_Doc_Parser_emphDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_emphDelimiter___closed__2);
v___x_2492_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___closed__1));
v___x_2493_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___closed__0));
v___x_2494_ = l_Lean_Parser_nodeWithAntiquot(v___x_2493_, v___x_2492_, v___x_2491_, v___x_2490_);
return v___x_2494_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter(void){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___closed__3, &l_Lean_Doc_Parser_emphDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_emphDelimiter___closed__3);
return v___x_2495_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = 42;
v___x_2503_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2502_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2504_ = 0;
v___x_2505_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___closed__2, &l_Lean_Doc_Parser_boldDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_boldDelimiter___closed__2);
v___x_2506_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___closed__1));
v___x_2507_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___closed__0));
v___x_2508_ = l_Lean_Parser_nodeWithAntiquot(v___x_2507_, v___x_2506_, v___x_2505_, v___x_2504_);
return v___x_2508_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter(void){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___closed__3, &l_Lean_Doc_Parser_boldDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_boldDelimiter___closed__3);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = 96;
v___x_2517_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2516_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2518_ = 0;
v___x_2519_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___closed__2, &l_Lean_Doc_Parser_codeDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___closed__2);
v___x_2520_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___closed__1));
v___x_2521_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___closed__0));
v___x_2522_ = l_Lean_Parser_nodeWithAntiquot(v___x_2521_, v___x_2520_, v___x_2519_, v___x_2518_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter(void){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___closed__3, &l_Lean_Doc_Parser_codeDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_codeDelimiter___closed__3);
return v___x_2523_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeBlockFence___closed__2(void){
_start:
{
uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2530_ = 0;
v___x_2531_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___closed__2, &l_Lean_Doc_Parser_codeDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___closed__2);
v___x_2532_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___closed__1));
v___x_2533_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___closed__0));
v___x_2534_ = l_Lean_Parser_nodeWithAntiquot(v___x_2533_, v___x_2532_, v___x_2531_, v___x_2530_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeBlockFence(void){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_obj_once(&l_Lean_Doc_Parser_codeBlockFence___closed__2, &l_Lean_Doc_Parser_codeBlockFence___closed__2_once, _init_l_Lean_Doc_Parser_codeBlockFence___closed__2);
return v___x_2535_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___closed__3(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___closed__2));
v___x_2544_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___closed__4(void){
_start:
{
uint8_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2545_ = 0;
v___x_2546_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___closed__3, &l_Lean_Doc_Parser_inlineMathMarker___closed__3_once, _init_l_Lean_Doc_Parser_inlineMathMarker___closed__3);
v___x_2547_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___closed__1));
v___x_2548_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___closed__0));
v___x_2549_ = l_Lean_Parser_nodeWithAntiquot(v___x_2548_, v___x_2547_, v___x_2546_, v___x_2545_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker(void){
_start:
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___closed__4, &l_Lean_Doc_Parser_inlineMathMarker___closed__4_once, _init_l_Lean_Doc_Parser_inlineMathMarker___closed__4);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___closed__3(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___closed__2));
v___x_2559_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___closed__4(void){
_start:
{
uint8_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2560_ = 0;
v___x_2561_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___closed__3, &l_Lean_Doc_Parser_displayMathMarker___closed__3_once, _init_l_Lean_Doc_Parser_displayMathMarker___closed__3);
v___x_2562_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___closed__1));
v___x_2563_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___closed__0));
v___x_2564_ = l_Lean_Parser_nodeWithAntiquot(v___x_2563_, v___x_2562_, v___x_2561_, v___x_2560_);
return v___x_2564_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker(void){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___closed__4, &l_Lean_Doc_Parser_displayMathMarker___closed__4_once, _init_l_Lean_Doc_Parser_displayMathMarker___closed__4);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___closed__2(void){
_start:
{
uint32_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = 58;
v___x_2573_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2572_);
return v___x_2573_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___closed__3(void){
_start:
{
uint8_t v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2574_ = 0;
v___x_2575_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___closed__2, &l_Lean_Doc_Parser_directiveDelimiter___closed__2_once, _init_l_Lean_Doc_Parser_directiveDelimiter___closed__2);
v___x_2576_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___closed__1));
v___x_2577_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___closed__0));
v___x_2578_ = l_Lean_Parser_nodeWithAntiquot(v___x_2577_, v___x_2576_, v___x_2575_, v___x_2574_);
return v___x_2578_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter(void){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___closed__3, &l_Lean_Doc_Parser_directiveDelimiter___closed__3_once, _init_l_Lean_Doc_Parser_directiveDelimiter___closed__3);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(lean_object* v_x_2580_){
_start:
{
if (lean_obj_tag(v_x_2580_) == 1)
{
lean_object* v_args_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_args_2581_ = lean_ctor_get(v_x_2580_, 2);
v___x_2582_ = lean_array_get_size(v_args_2581_);
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2584_ = lean_nat_dec_eq(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_box(0);
return v___x_2585_;
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = lean_array_fget_borrowed(v_args_2581_, v___x_2586_);
if (lean_obj_tag(v___x_2587_) == 2)
{
lean_object* v_val_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_val_2588_ = lean_ctor_get(v___x_2587_, 1);
v___x_2589_ = lean_string_length(v_val_2588_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_box(0);
return v___x_2591_;
}
}
}
else
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_box(0);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength___boxed(lean_object* v_x_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_x_2593_);
lean_dec(v_x_2593_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(uint32_t v_ch_2595_, lean_object* v_x_2596_, lean_object* v_x_2597_){
_start:
{
lean_object* v_zero_2598_; uint8_t v_isZero_2599_; 
v_zero_2598_ = lean_unsigned_to_nat(0u);
v_isZero_2599_ = lean_nat_dec_eq(v_x_2596_, v_zero_2598_);
if (v_isZero_2599_ == 1)
{
lean_dec(v_x_2596_);
return v_x_2597_;
}
else
{
lean_object* v_one_2600_; lean_object* v_n_2601_; lean_object* v___x_2602_; 
v_one_2600_ = lean_unsigned_to_nat(1u);
v_n_2601_ = lean_nat_sub(v_x_2596_, v_one_2600_);
lean_dec(v_x_2596_);
v___x_2602_ = lean_string_push(v_x_2597_, v_ch_2595_);
v_x_2596_ = v_n_2601_;
v_x_2597_ = v___x_2602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0___boxed(lean_object* v_ch_2604_, lean_object* v_x_2605_, lean_object* v_x_2606_){
_start:
{
uint32_t v_ch_boxed_2607_; lean_object* v_res_2608_; 
v_ch_boxed_2607_ = lean_unbox_uint32(v_ch_2604_);
lean_dec(v_ch_2604_);
v_res_2608_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_boxed_2607_, v_x_2605_, v_x_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(lean_object* v_delim_2611_, uint32_t v_ch_2612_, lean_object* v_contents_2613_, lean_object* v_c_2614_, lean_object* v_s_2615_){
_start:
{
lean_object* v_fn_2616_; lean_object* v_s_2617_; lean_object* v_stxStack_2618_; lean_object* v_errorMsg_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_fn_2616_ = lean_ctor_get(v_delim_2611_, 1);
lean_inc_ref_n(v_fn_2616_, 2);
lean_dec_ref(v_delim_2611_);
lean_inc_ref(v_c_2614_);
v_s_2617_ = lean_apply_2(v_fn_2616_, v_c_2614_, v_s_2615_);
v_stxStack_2618_ = lean_ctor_get(v_s_2617_, 0);
lean_inc_ref(v_stxStack_2618_);
v_errorMsg_2619_ = lean_ctor_get(v_s_2617_, 4);
lean_inc(v_errorMsg_2619_);
v___x_2620_ = lean_box(0);
v___x_2621_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2619_, v___x_2620_);
lean_dec(v_errorMsg_2619_);
if (v___x_2621_ == 0)
{
lean_dec_ref(v_stxStack_2618_);
lean_dec_ref(v_fn_2616_);
lean_dec_ref(v_c_2614_);
lean_dec_ref(v_contents_2613_);
return v_s_2617_;
}
else
{
lean_object* v_fn_2622_; lean_object* v_s_2623_; lean_object* v_pos_2624_; lean_object* v_errorMsg_2625_; uint8_t v___x_2626_; 
v_fn_2622_ = lean_ctor_get(v_contents_2613_, 1);
lean_inc_ref(v_fn_2622_);
lean_dec_ref(v_contents_2613_);
lean_inc_ref(v_c_2614_);
v_s_2623_ = lean_apply_2(v_fn_2622_, v_c_2614_, v_s_2617_);
v_pos_2624_ = lean_ctor_get(v_s_2623_, 2);
lean_inc(v_pos_2624_);
v_errorMsg_2625_ = lean_ctor_get(v_s_2623_, 4);
lean_inc(v_errorMsg_2625_);
v___x_2626_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2625_, v___x_2620_);
lean_dec(v_errorMsg_2625_);
if (v___x_2626_ == 0)
{
lean_dec(v_pos_2624_);
lean_dec_ref(v_stxStack_2618_);
lean_dec_ref(v_fn_2616_);
lean_dec_ref(v_c_2614_);
return v_s_2623_;
}
else
{
lean_object* v_s_2627_; lean_object* v_stxStack_2628_; lean_object* v_errorMsg_2629_; uint8_t v___x_2630_; 
v_s_2627_ = lean_apply_2(v_fn_2616_, v_c_2614_, v_s_2623_);
v_stxStack_2628_ = lean_ctor_get(v_s_2627_, 0);
lean_inc_ref(v_stxStack_2628_);
v_errorMsg_2629_ = lean_ctor_get(v_s_2627_, 4);
lean_inc(v_errorMsg_2629_);
v___x_2630_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2629_, v___x_2620_);
lean_dec(v_errorMsg_2629_);
if (v___x_2630_ == 0)
{
lean_dec_ref(v_stxStack_2628_);
lean_dec(v_pos_2624_);
lean_dec_ref(v_stxStack_2618_);
return v_s_2627_;
}
else
{
lean_object* v_opener_2631_; lean_object* v___x_2632_; 
v_opener_2631_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2618_);
lean_dec_ref(v_stxStack_2618_);
v___x_2632_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_opener_2631_);
lean_dec(v_opener_2631_);
if (lean_obj_tag(v___x_2632_) == 1)
{
lean_object* v_val_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_val_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2628_);
lean_dec_ref(v_stxStack_2628_);
v___x_2635_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v___x_2634_);
lean_dec(v___x_2634_);
if (lean_obj_tag(v___x_2635_) == 1)
{
lean_object* v_val_2636_; uint8_t v___x_2637_; 
v_val_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = lean_nat_dec_eq(v_val_2633_, v_val_2636_);
lean_dec(v_val_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2638_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2639_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2640_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_2612_, v_val_2633_, v___x_2639_);
v___x_2641_ = lean_string_append(v___x_2638_, v___x_2640_);
v___x_2642_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0));
v___x_2643_ = lean_string_append(v___x_2641_, v___x_2642_);
v___x_2644_ = lean_string_append(v___x_2643_, v___x_2640_);
lean_dec_ref(v___x_2640_);
v___x_2645_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1));
v___x_2646_ = lean_string_append(v___x_2644_, v___x_2645_);
v___x_2647_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2627_, v___x_2646_, v_pos_2624_, v___x_2620_);
return v___x_2647_;
}
else
{
lean_dec(v_val_2633_);
lean_dec(v_pos_2624_);
return v_s_2627_;
}
}
else
{
lean_dec(v___x_2635_);
lean_dec(v_val_2633_);
lean_dec(v_pos_2624_);
return v_s_2627_;
}
}
else
{
lean_dec(v___x_2632_);
lean_dec_ref(v_stxStack_2628_);
lean_dec(v_pos_2624_);
return v_s_2627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed(lean_object* v_delim_2648_, lean_object* v_ch_2649_, lean_object* v_contents_2650_, lean_object* v_c_2651_, lean_object* v_s_2652_){
_start:
{
uint32_t v_ch_boxed_2653_; lean_object* v_res_2654_; 
v_ch_boxed_2653_ = lean_unbox_uint32(v_ch_2649_);
lean_dec(v_ch_2649_);
v_res_2654_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(v_delim_2648_, v_ch_boxed_2653_, v_contents_2650_, v_c_2651_, v_s_2652_);
return v_res_2654_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = 96;
v___x_2663_ = lean_box_uint32(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2664_ = l_Lean_Doc_Parser_versoCode;
v___x_2665_ = l_Lean_Doc_Parser_codeDelimiter;
v___x_2666_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2___boxed__const__1;
v___x_2667_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_2667_, 0, v___x_2665_);
lean_closure_set(v___x_2667_, 1, v___x_2666_);
lean_closure_set(v___x_2667_, 2, v___x_2664_);
return v___x_2667_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3(void){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__2);
v___x_2669_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v___x_2668_);
return v___x_2670_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4(void){
_start:
{
uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2671_ = 0;
v___x_2672_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__3);
v___x_2673_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1));
v___x_2674_ = ((lean_object*)(l_Lean_Doc_Syntax_code___closed__0));
v___x_2675_ = l_Lean_Parser_nodeWithAntiquot(v___x_2674_, v___x_2673_, v___x_2672_, v___x_2671_);
return v___x_2675_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode(void){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__4);
return v___x_2676_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1(void){
_start:
{
uint32_t v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = 10;
v___x_2684_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2683_);
return v___x_2684_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2(void){
_start:
{
uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2685_ = 0;
v___x_2686_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1);
v___x_2687_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0));
v___x_2688_ = ((lean_object*)(l_Lean_Doc_Syntax_linebreak___closed__0));
v___x_2689_ = l_Lean_Parser_nodeWithAntiquot(v___x_2688_, v___x_2687_, v___x_2686_, v___x_2685_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v___x_2692_; lean_object* v_fn_2693_; lean_object* v___x_2694_; 
v___x_2692_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2);
v_fn_2693_ = lean_ctor_get(v___x_2692_, 1);
lean_inc_ref(v_fn_2693_);
v___x_2694_ = lean_apply_2(v_fn_2693_, v_a_2690_, v_a_2691_);
return v___x_2694_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1));
v___x_2703_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2702_);
return v___x_2703_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__5));
v___x_2705_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2704_);
return v___x_2705_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = l_Lean_Doc_Parser_linkTarget;
v___x_2707_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_2708_ = l_Lean_Parser_andthen(v___x_2707_, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_2710_ = l_Lean_Doc_Parser_versoImageAlt;
v___x_2711_ = l_Lean_Parser_andthen(v___x_2710_, v___x_2709_);
return v___x_2711_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5);
v___x_2713_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2);
v___x_2714_ = l_Lean_Parser_andthen(v___x_2713_, v___x_2712_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7(void){
_start:
{
uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2715_ = 0;
v___x_2716_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6);
v___x_2717_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_2718_ = ((lean_object*)(l_Lean_Doc_Syntax_image___closed__0));
v___x_2719_ = l_Lean_Parser_nodeWithAntiquot(v___x_2718_, v___x_2717_, v___x_2716_, v___x_2715_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object* v_a_2720_, lean_object* v_a_2721_){
_start:
{
lean_object* v___x_2722_; lean_object* v_fn_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7);
v_fn_2723_ = lean_ctor_get(v___x_2722_, 1);
lean_inc_ref(v_fn_2723_);
v___x_2724_ = lean_apply_2(v_fn_2723_, v_a_2720_, v_a_2721_);
return v___x_2724_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1(void){
_start:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__2));
v___x_2732_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2731_);
return v___x_2732_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_2734_ = l_Lean_Doc_Parser_versoRef;
v___x_2735_ = l_Lean_Parser_andthen(v___x_2734_, v___x_2733_);
return v___x_2735_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2);
v___x_2737_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1);
v___x_2738_ = l_Lean_Parser_andthen(v___x_2737_, v___x_2736_);
return v___x_2738_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4(void){
_start:
{
uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2739_ = 0;
v___x_2740_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3);
v___x_2741_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_2742_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote___closed__0));
v___x_2743_ = l_Lean_Parser_nodeWithAntiquot(v___x_2742_, v___x_2741_, v___x_2740_, v___x_2739_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2746_; lean_object* v_fn_2747_; lean_object* v___x_2748_; 
v___x_2746_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4);
v_fn_2747_ = lean_ctor_get(v___x_2746_, 1);
lean_inc_ref(v_fn_2747_);
v___x_2748_ = lean_apply_2(v_fn_2747_, v_a_2744_, v_a_2745_);
return v___x_2748_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2755_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
v___x_2756_ = l_Lean_Doc_Parser_inlineMathMarker;
v___x_2757_ = l_Lean_Parser_andthen(v___x_2756_, v___x_2755_);
return v___x_2757_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2(void){
_start:
{
uint8_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2758_ = 0;
v___x_2759_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1);
v___x_2760_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_2761_ = ((lean_object*)(l_Lean_Doc_Syntax_inline__math___closed__0));
v___x_2762_ = l_Lean_Parser_nodeWithAntiquot(v___x_2761_, v___x_2760_, v___x_2759_, v___x_2758_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2765_; lean_object* v_fn_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2);
v_fn_2766_ = lean_ctor_get(v___x_2765_, 1);
lean_inc_ref(v_fn_2766_);
v___x_2767_ = lean_apply_2(v_fn_2766_, v_a_2763_, v_a_2764_);
return v___x_2767_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1(void){
_start:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2774_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
v___x_2775_ = l_Lean_Doc_Parser_displayMathMarker;
v___x_2776_ = l_Lean_Parser_andthen(v___x_2775_, v___x_2774_);
return v___x_2776_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2(void){
_start:
{
uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2777_ = 0;
v___x_2778_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1);
v___x_2779_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_2780_ = ((lean_object*)(l_Lean_Doc_Syntax_display__math___closed__0));
v___x_2781_ = l_Lean_Parser_nodeWithAntiquot(v___x_2780_, v___x_2779_, v___x_2778_, v___x_2777_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot(lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
lean_object* v___x_2784_; lean_object* v_fn_2785_; lean_object* v___x_2786_; 
v___x_2784_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2);
v_fn_2785_ = lean_ctor_get(v___x_2784_, 1);
lean_inc_ref(v_fn_2785_);
v___x_2786_ = lean_apply_2(v_fn_2785_, v_a_2782_, v_a_2783_);
return v___x_2786_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2787_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot), 2, 0);
v___x_2788_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
lean_ctor_set(v___x_2789_, 1, v___x_2787_);
return v___x_2789_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
v___x_2791_ = l_Lean_Parser_atomic(v___x_2790_);
return v___x_2791_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2792_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot), 2, 0);
v___x_2793_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v___x_2792_);
return v___x_2794_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2795_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
v___x_2796_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1);
v___x_2797_ = l_Lean_Parser_orelse(v___x_2796_, v___x_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot(lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v_fn_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3);
v_fn_2801_ = lean_ctor_get(v___x_2800_, 1);
lean_inc_ref(v_fn_2801_);
v___x_2802_ = lean_apply_2(v_fn_2801_, v_a_2798_, v_a_2799_);
return v___x_2802_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1(void){
_start:
{
uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2809_ = 0;
v___x_2810_ = l_Lean_Doc_Parser_versoText;
v___x_2811_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0));
v___x_2812_ = ((lean_object*)(l_Lean_Doc_Syntax_text___closed__0));
v___x_2813_ = l_Lean_Parser_nodeWithAntiquot(v___x_2812_, v___x_2811_, v___x_2810_, v___x_2809_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v___x_2816_; lean_object* v_fn_2817_; lean_object* v___x_2818_; 
v___x_2816_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1);
v_fn_2817_ = lean_ctor_get(v___x_2816_, 1);
lean_inc_ref(v_fn_2817_);
v___x_2818_ = lean_apply_2(v_fn_2817_, v_a_2814_, v_a_2815_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object* v___y_2819_){
_start:
{
lean_inc(v___y_2819_);
return v___y_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(v___y_2820_);
lean_dec(v___y_2820_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object* v___y_2822_){
_start:
{
lean_inc_ref(v___y_2822_);
return v___y_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object* v___y_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(v___y_2823_);
lean_dec_ref(v___y_2823_);
return v_res_2824_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = 42;
v___x_2838_ = lean_box_uint32(v___x_2837_);
return v___x_2838_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2839_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_2840_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v___x_2839_);
return v___x_2841_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = 95;
v___x_2849_ = lean_box_uint32(v___x_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v_fn_2865_; lean_object* v___x_2866_; 
v___x_2852_ = ((lean_object*)(l_Lean_Doc_Syntax_emph___closed__0));
v___x_2853_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_2854_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2855_ = l_Lean_Doc_Parser_emphDelimiter;
v___x_2856_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2854_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Lean_Parser_atomic(v___x_2857_);
v___x_2859_ = l_Lean_Parser_many(v___x_2858_);
v___x_2860_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
v___x_2861_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_2861_, 0, v___x_2855_);
lean_closure_set(v___x_2861_, 1, v___x_2860_);
lean_closure_set(v___x_2861_, 2, v___x_2859_);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2854_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = 0;
v___x_2864_ = l_Lean_Parser_nodeWithAntiquot(v___x_2852_, v___x_2853_, v___x_2862_, v___x_2863_);
v_fn_2865_ = lean_ctor_get(v___x_2864_, 1);
lean_inc_ref(v_fn_2865_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = lean_apply_2(v_fn_2865_, v_a_2850_, v_a_2851_);
return v___x_2866_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot), 2, 0);
v___x_2868_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2867_);
return v___x_2869_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_2871_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
lean_ctor_set(v___x_2872_, 1, v___x_2870_);
return v___x_2872_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1(void){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__2));
v___x_2880_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; lean_object* v___x_2895_; lean_object* v_fn_2896_; lean_object* v___x_2897_; 
v___x_2883_ = ((lean_object*)(l_Lean_Doc_Syntax_link___closed__0));
v___x_2884_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_2885_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_2886_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2887_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2886_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = l_Lean_Parser_atomic(v___x_2888_);
v___x_2890_ = l_Lean_Parser_many(v___x_2889_);
v___x_2891_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_2892_ = l_Lean_Parser_andthen(v___x_2890_, v___x_2891_);
v___x_2893_ = l_Lean_Parser_andthen(v___x_2885_, v___x_2892_);
v___x_2894_ = 0;
v___x_2895_ = l_Lean_Parser_nodeWithAntiquot(v___x_2883_, v___x_2884_, v___x_2893_, v___x_2894_);
v_fn_2896_ = lean_ctor_get(v___x_2895_, 1);
lean_inc_ref(v_fn_2896_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = lean_apply_2(v_fn_2896_, v_a_2881_, v_a_2882_);
return v___x_2897_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_2899_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
return v___x_2900_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5(void){
_start:
{
uint8_t v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2906_ = 1;
v___x_2907_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4));
v___x_2908_ = ((lean_object*)(l_Lean_Doc_Syntax_inline_quot___closed__0));
v___x_2909_ = l_Lean_Parser_mkAntiquot(v___x_2908_, v___x_2907_, v___x_2906_, v___x_2906_);
return v___x_2909_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_2911_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___x_2910_);
return v___x_2912_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1(void){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__6));
v___x_2920_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2919_);
return v___x_2920_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2(void){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = l_Lean_Doc_Parser_arg;
v___x_2922_ = l_Lean_Parser_many(v___x_2921_);
return v___x_2922_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__7));
v___x_2924_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2923_);
return v___x_2924_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_2929_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2930_ = l_Lean_Parser_node(v___x_2929_, v___x_2928_);
return v___x_2930_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_2932_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2933_ = l_Lean_Parser_node(v___x_2932_, v___x_2931_);
return v___x_2933_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = l_Lean_Parser_skip;
v___x_2935_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2936_ = l_Lean_Parser_node(v___x_2935_, v___x_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot(lean_object* v_a_2937_, lean_object* v_a_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v_fn_2965_; lean_object* v___x_2966_; 
v___x_2939_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__0));
v___x_2940_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_2941_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1);
v___x_2942_ = l_Lean_Parser_ident;
v___x_2943_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_2944_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_2945_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6);
v___x_2946_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2947_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = l_Lean_Parser_atomic(v___x_2948_);
lean_inc_ref(v___x_2949_);
v___x_2950_ = l_Lean_Parser_many(v___x_2949_);
v___x_2951_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7);
v___x_2952_ = l_Lean_Parser_andthen(v___x_2950_, v___x_2951_);
v___x_2953_ = l_Lean_Parser_andthen(v___x_2945_, v___x_2952_);
v___x_2954_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8);
v___x_2955_ = l_Lean_Parser_many1(v___x_2949_);
v___x_2956_ = l_Lean_Parser_andthen(v___x_2955_, v___x_2954_);
v___x_2957_ = l_Lean_Parser_andthen(v___x_2954_, v___x_2956_);
v___x_2958_ = l_Lean_Parser_orelse(v___x_2953_, v___x_2957_);
v___x_2959_ = l_Lean_Parser_andthen(v___x_2944_, v___x_2958_);
v___x_2960_ = l_Lean_Parser_andthen(v___x_2943_, v___x_2959_);
v___x_2961_ = l_Lean_Parser_andthen(v___x_2942_, v___x_2960_);
v___x_2962_ = l_Lean_Parser_andthen(v___x_2941_, v___x_2961_);
v___x_2963_ = 0;
v___x_2964_ = l_Lean_Parser_nodeWithAntiquot(v___x_2939_, v___x_2940_, v___x_2962_, v___x_2963_);
v_fn_2965_ = lean_ctor_get(v___x_2964_, 1);
lean_inc_ref(v_fn_2965_);
lean_dec_ref(v___x_2964_);
v___x_2966_ = lean_apply_2(v_fn_2965_, v_a_2937_, v_a_2938_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot(lean_object* v_c_2967_, lean_object* v_s_2968_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_fn_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v_alts_2994_; lean_object* v_fn_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2969_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2970_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0);
v___x_2971_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot), 2, 0);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2969_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
v___x_2973_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot), 2, 0);
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2969_);
lean_ctor_set(v___x_2974_, 1, v___x_2973_);
v___x_2975_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1);
v___x_2976_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2);
v___x_2977_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot), 2, 0);
v___x_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2969_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3);
v___x_2980_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5);
v_fn_2981_ = lean_ctor_get(v___x_2980_, 1);
v___x_2982_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6);
v___x_2983_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
v___x_2984_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot), 2, 0);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2969_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
v___x_2986_ = l_Lean_Parser_orelse(v___x_2982_, v___x_2985_);
v___x_2987_ = l_Lean_Parser_orelse(v___x_2979_, v___x_2986_);
v___x_2988_ = l_Lean_Parser_orelse(v___x_2978_, v___x_2987_);
v___x_2989_ = l_Lean_Parser_orelse(v___x_2976_, v___x_2988_);
v___x_2990_ = l_Lean_Parser_orelse(v___x_2975_, v___x_2989_);
v___x_2991_ = l_Lean_Parser_orelse(v___x_2983_, v___x_2990_);
v___x_2992_ = l_Lean_Parser_orelse(v___x_2974_, v___x_2991_);
v___x_2993_ = l_Lean_Parser_orelse(v___x_2972_, v___x_2992_);
v_alts_2994_ = l_Lean_Parser_orelse(v___x_2970_, v___x_2993_);
v_fn_2995_ = lean_ctor_get(v_alts_2994_, 1);
lean_inc_ref(v_fn_2995_);
lean_dec_ref(v_alts_2994_);
v___x_2996_ = 0;
lean_inc_ref(v_fn_2981_);
v___x_2997_ = l_Lean_Parser_withAntiquotFn(v_fn_2981_, v_fn_2995_, v___x_2996_, v_c_2967_, v_s_2968_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot(lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v_fn_3013_; lean_object* v___x_3014_; 
v___x_3000_ = ((lean_object*)(l_Lean_Doc_Syntax_bold___closed__0));
v___x_3001_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_3002_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3003_ = l_Lean_Doc_Parser_boldDelimiter;
v___x_3004_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3002_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = l_Lean_Parser_atomic(v___x_3005_);
v___x_3007_ = l_Lean_Parser_many(v___x_3006_);
v___x_3008_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
v___x_3009_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_3009_, 0, v___x_3003_);
lean_closure_set(v___x_3009_, 1, v___x_3008_);
lean_closure_set(v___x_3009_, 2, v___x_3007_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3002_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = 0;
v___x_3012_ = l_Lean_Parser_nodeWithAntiquot(v___x_3000_, v___x_3001_, v___x_3010_, v___x_3011_);
v_fn_3013_ = lean_ctor_get(v___x_3012_, 1);
lean_inc_ref(v_fn_3013_);
lean_dec_ref(v___x_3012_);
v___x_3014_ = lean_apply_2(v_fn_3013_, v_a_2998_, v_a_2999_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text___closed__0(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_3016_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
return v___x_3017_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text(void){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_text___closed__0, &l_Lean_Doc_Parser_Inline_text___closed__0_once, _init_l_Lean_Doc_Parser_Inline_text___closed__0);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1(){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_3026_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0));
v___x_3027_ = l_Lean_addBuiltinDocString(v___x_3025_, v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1(){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_3037_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0));
v___x_3038_ = l_Lean_addBuiltinDocString(v___x_3036_, v___x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
return v_res_3040_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_code(void){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode;
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1(){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1));
v___x_3044_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0));
v___x_3045_ = l_Lean_addBuiltinDocString(v___x_3043_, v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object* v_a_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
return v_res_3047_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_inline__math(void){
_start:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1(){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_3051_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0));
v___x_3052_ = l_Lean_addBuiltinDocString(v___x_3050_, v___x_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
return v_res_3054_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_display__math(void){
_start:
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1(){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_3058_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0));
v___x_3059_ = l_Lean_addBuiltinDocString(v___x_3057_, v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1(){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_3069_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0));
v___x_3070_ = l_Lean_addBuiltinDocString(v___x_3068_, v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object* v_a_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
return v_res_3072_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image___closed__0(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_3074_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
return v___x_3075_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image(void){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_image___closed__0, &l_Lean_Doc_Parser_Inline_image___closed__0_once, _init_l_Lean_Doc_Parser_Inline_image___closed__0);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1(){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_3079_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0));
v___x_3080_ = l_Lean_addBuiltinDocString(v___x_3078_, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object* v_a_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
return v_res_3082_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote___closed__0(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_3084_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3083_);
return v___x_3085_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote(void){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_footnote___closed__0, &l_Lean_Doc_Parser_Inline_footnote___closed__0_once, _init_l_Lean_Doc_Parser_Inline_footnote___closed__0);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1(){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3088_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_3089_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0));
v___x_3090_ = l_Lean_addBuiltinDocString(v___x_3088_, v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___boxed(lean_object* v_a_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
return v_res_3092_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3093_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_3094_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v___x_3093_);
return v___x_3095_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak(void){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_linebreak___closed__0, &l_Lean_Doc_Parser_Inline_linebreak___closed__0_once, _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1(){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_3104_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0));
v___x_3105_ = l_Lean_addBuiltinDocString(v___x_3103_, v___x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
return v_res_3107_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2(void){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = ((lean_object*)(l_Lean_Doc_Parser_inline___closed__1));
v___x_3121_ = l_Lean_Parser_atomic(v___x_3120_);
return v___x_3121_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3(void){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2);
v___x_3123_ = l_Lean_Parser_many1(v___x_3122_);
return v___x_3123_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4(void){
_start:
{
uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3124_ = 0;
v___x_3125_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_3126_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1));
v___x_3127_ = ((lean_object*)(l_Lean_Doc_Syntax_para___closed__0));
v___x_3128_ = l_Lean_Parser_nodeWithAntiquot(v___x_3127_, v___x_3126_, v___x_3125_, v___x_3124_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3131_; lean_object* v_fn_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4);
v_fn_3132_ = lean_ctor_get(v___x_3131_, 1);
lean_inc_ref(v_fn_3132_);
v___x_3133_ = lean_apply_2(v_fn_3132_, v_a_3129_, v_a_3130_);
return v___x_3133_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1(void){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_3141_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3142_ = l_Lean_Parser_andthen(v___x_3141_, v___x_3140_);
return v___x_3142_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1);
v___x_3144_ = l_Lean_Parser_ident;
v___x_3145_ = l_Lean_Parser_andthen(v___x_3144_, v___x_3143_);
return v___x_3145_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2);
v___x_3147_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1);
v___x_3148_ = l_Lean_Parser_andthen(v___x_3147_, v___x_3146_);
return v___x_3148_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4(void){
_start:
{
uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = 0;
v___x_3150_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3);
v___x_3151_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_3152_ = ((lean_object*)(l_Lean_Doc_Syntax_command___closed__0));
v___x_3153_ = l_Lean_Parser_nodeWithAntiquot(v___x_3152_, v___x_3151_, v___x_3150_, v___x_3149_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___x_3156_; lean_object* v_fn_3157_; lean_object* v___x_3158_; 
v___x_3156_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4);
v_fn_3157_ = lean_ctor_get(v___x_3156_, 1);
lean_inc_ref(v_fn_3157_);
v___x_3158_ = lean_apply_2(v_fn_3157_, v_a_3154_, v_a_3155_);
return v___x_3158_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__2));
v___x_3166_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1);
v___x_3168_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit;
v___x_3169_ = l_Lean_Parser_andthen(v___x_3168_, v___x_3167_);
return v___x_3169_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2);
v___x_3171_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1);
v___x_3172_ = l_Lean_Parser_andthen(v___x_3171_, v___x_3170_);
return v___x_3172_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4(void){
_start:
{
uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3173_ = 0;
v___x_3174_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3);
v___x_3175_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_3176_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__0));
v___x_3177_ = l_Lean_Parser_nodeWithAntiquot(v___x_3176_, v___x_3175_, v___x_3174_, v___x_3173_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3180_; lean_object* v_fn_3181_; lean_object* v___x_3182_; 
v___x_3180_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4);
v_fn_3181_ = lean_ctor_get(v___x_3180_, 1);
lean_inc_ref(v_fn_3181_);
v___x_3182_ = lean_apply_2(v_fn_3181_, v_a_3178_, v_a_3179_);
return v___x_3182_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__2));
v___x_3190_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3189_);
return v___x_3190_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = l_Lean_Doc_Parser_versoLinkRefUrl;
v___x_3192_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1);
v___x_3193_ = l_Lean_Parser_andthen(v___x_3192_, v___x_3191_);
return v___x_3193_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2);
v___x_3195_ = l_Lean_Doc_Parser_versoRef;
v___x_3196_ = l_Lean_Parser_andthen(v___x_3195_, v___x_3194_);
return v___x_3196_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4(void){
_start:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3);
v___x_3198_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_3199_ = l_Lean_Parser_andthen(v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5(void){
_start:
{
uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3200_ = 0;
v___x_3201_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4);
v___x_3202_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_3203_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__0));
v___x_3204_ = l_Lean_Parser_nodeWithAntiquot(v___x_3203_, v___x_3202_, v___x_3201_, v___x_3200_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3207_; lean_object* v_fn_3208_; lean_object* v___x_3209_; 
v___x_3207_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5);
v_fn_3208_ = lean_ctor_get(v___x_3207_, 1);
lean_inc_ref(v_fn_3208_);
v___x_3209_ = lean_apply_2(v_fn_3208_, v_a_3205_, v_a_3206_);
return v___x_3209_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2);
v___x_3217_ = l_Lean_Parser_many(v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3218_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1);
v___x_3219_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1);
v___x_3220_ = l_Lean_Parser_andthen(v___x_3219_, v___x_3218_);
return v___x_3220_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2);
v___x_3222_ = l_Lean_Doc_Parser_versoRef;
v___x_3223_ = l_Lean_Parser_andthen(v___x_3222_, v___x_3221_);
return v___x_3223_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3);
v___x_3225_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1);
v___x_3226_ = l_Lean_Parser_andthen(v___x_3225_, v___x_3224_);
return v___x_3226_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5(void){
_start:
{
uint8_t v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3227_ = 0;
v___x_3228_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4);
v___x_3229_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_3230_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__0));
v___x_3231_ = l_Lean_Parser_nodeWithAntiquot(v___x_3230_, v___x_3229_, v___x_3228_, v___x_3227_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v___x_3234_; lean_object* v_fn_3235_; lean_object* v___x_3236_; 
v___x_3234_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5);
v_fn_3235_ = lean_ctor_get(v___x_3234_, 1);
lean_inc_ref(v_fn_3235_);
v___x_3236_ = lean_apply_2(v_fn_3235_, v_a_3232_, v_a_3233_);
return v___x_3236_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3243_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_3244_ = l_Lean_Doc_Parser_headerMarker;
v___x_3245_ = l_Lean_Parser_andthen(v___x_3244_, v___x_3243_);
return v___x_3245_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2(void){
_start:
{
uint8_t v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3246_ = 0;
v___x_3247_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1);
v___x_3248_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_3249_ = ((lean_object*)(l_Lean_Doc_Syntax_header___closed__0));
v___x_3250_ = l_Lean_Parser_nodeWithAntiquot(v___x_3249_, v___x_3248_, v___x_3247_, v___x_3246_);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v___x_3253_; lean_object* v_fn_3254_; lean_object* v___x_3255_; 
v___x_3253_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2);
v_fn_3254_ = lean_ctor_get(v___x_3253_, 1);
lean_inc_ref(v_fn_3254_);
v___x_3255_ = lean_apply_2(v_fn_3254_, v_a_3251_, v_a_3252_);
return v___x_3255_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3263_ = l_Lean_Parser_ident;
v___x_3264_ = l_Lean_Parser_andthen(v___x_3263_, v___x_3262_);
return v___x_3264_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1);
v___x_3266_ = l_Lean_Parser_optional(v___x_3265_);
return v___x_3266_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; 
v___x_3267_ = l_Lean_Doc_Parser_codeBlockFence;
v___x_3268_ = l_Lean_Doc_Parser_versoCodeBlock;
v___x_3269_ = l_Lean_Parser_andthen(v___x_3268_, v___x_3267_);
return v___x_3269_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3);
v___x_3271_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2);
v___x_3272_ = l_Lean_Parser_andthen(v___x_3271_, v___x_3270_);
return v___x_3272_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4);
v___x_3274_ = l_Lean_Doc_Parser_codeBlockFence;
v___x_3275_ = l_Lean_Parser_andthen(v___x_3274_, v___x_3273_);
return v___x_3275_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6(void){
_start:
{
uint8_t v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3276_ = 0;
v___x_3277_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5);
v___x_3278_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_3279_ = ((lean_object*)(l_Lean_Doc_Syntax_codeblock___closed__0));
v___x_3280_ = l_Lean_Parser_nodeWithAntiquot(v___x_3279_, v___x_3278_, v___x_3277_, v___x_3276_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object* v_a_3281_, lean_object* v_a_3282_){
_start:
{
lean_object* v___x_3283_; lean_object* v_fn_3284_; lean_object* v___x_3285_; 
v___x_3283_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6);
v_fn_3284_ = lean_ctor_get(v___x_3283_, 1);
lean_inc_ref(v_fn_3284_);
v___x_3285_ = lean_apply_2(v_fn_3284_, v_a_3281_, v_a_3282_);
return v___x_3285_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4(void){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3));
v___x_3305_ = l_Lean_Parser_atomic(v___x_3304_);
return v___x_3305_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4);
v___x_3307_ = l_Lean_Parser_many(v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object* v_marker_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; lean_object* v___x_3334_; lean_object* v_fn_3335_; lean_object* v___x_3336_; 
v___x_3325_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0));
v___x_3326_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_3327_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3328_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_Parser_atomic(v___x_3329_);
v___x_3331_ = l_Lean_Parser_many(v___x_3330_);
v___x_3332_ = l_Lean_Parser_andthen(v_marker_3322_, v___x_3331_);
v___x_3333_ = 0;
v___x_3334_ = l_Lean_Parser_nodeWithAntiquot(v___x_3325_, v___x_3326_, v___x_3332_, v___x_3333_);
v_fn_3335_ = lean_ctor_get(v___x_3334_, 1);
lean_inc_ref(v_fn_3335_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = lean_apply_2(v_fn_3335_, v_a_3323_, v_a_3324_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v_fn_3349_; lean_object* v___x_3350_; 
v___x_3339_ = ((lean_object*)(l_Lean_Doc_Syntax_ul___closed__0));
v___x_3340_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_3341_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3342_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker;
v___x_3343_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3343_, 0, v___x_3342_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3341_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = l_Lean_Parser_atomic(v___x_3344_);
v___x_3346_ = l_Lean_Parser_many1(v___x_3345_);
v___x_3347_ = 0;
v___x_3348_ = l_Lean_Parser_nodeWithAntiquot(v___x_3339_, v___x_3340_, v___x_3346_, v___x_3347_);
v_fn_3349_ = lean_ctor_get(v___x_3348_, 1);
lean_inc_ref(v_fn_3349_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = lean_apply_2(v_fn_3349_, v_a_3337_, v_a_3338_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v_fn_3369_; lean_object* v___x_3370_; 
v___x_3359_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__0));
v___x_3360_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_3361_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3362_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker;
v___x_3363_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3363_, 0, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3361_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = l_Lean_Parser_atomic(v___x_3364_);
v___x_3366_ = l_Lean_Parser_many1(v___x_3365_);
v___x_3367_ = 0;
v___x_3368_ = l_Lean_Parser_nodeWithAntiquot(v___x_3359_, v___x_3360_, v___x_3366_, v___x_3367_);
v_fn_3369_ = lean_ctor_get(v___x_3368_, 1);
lean_inc_ref(v_fn_3369_);
lean_dec_ref(v___x_3368_);
v___x_3370_ = lean_apply_2(v_fn_3369_, v_a_3357_, v_a_3358_);
return v___x_3370_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__2));
v___x_3378_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v_fn_3392_; lean_object* v___x_3393_; 
v___x_3381_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__0));
v___x_3382_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_3383_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1);
v___x_3384_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3385_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = l_Lean_Parser_atomic(v___x_3386_);
v___x_3388_ = l_Lean_Parser_many(v___x_3387_);
v___x_3389_ = l_Lean_Parser_andthen(v___x_3383_, v___x_3388_);
v___x_3390_ = 0;
v___x_3391_ = l_Lean_Parser_nodeWithAntiquot(v___x_3381_, v___x_3382_, v___x_3389_, v___x_3390_);
v_fn_3392_ = lean_ctor_get(v___x_3391_, 1);
lean_inc_ref(v_fn_3392_);
lean_dec_ref(v___x_3391_);
v___x_3393_ = lean_apply_2(v_fn_3392_, v_a_3379_, v_a_3380_);
return v___x_3393_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_3395_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; lean_object* v___x_3420_; lean_object* v_fn_3421_; lean_object* v___x_3422_; 
v___x_3405_ = ((lean_object*)(l_Lean_Doc_Syntax_directive___closed__0));
v___x_3406_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_3407_ = l_Lean_Doc_Parser_directiveDelimiter;
v___x_3408_ = l_Lean_Parser_ident;
v___x_3409_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3410_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3411_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = l_Lean_Parser_atomic(v___x_3412_);
v___x_3414_ = l_Lean_Parser_many(v___x_3413_);
v___x_3415_ = l_Lean_Parser_andthen(v___x_3414_, v___x_3407_);
v___x_3416_ = l_Lean_Parser_andthen(v___x_3409_, v___x_3415_);
v___x_3417_ = l_Lean_Parser_andthen(v___x_3408_, v___x_3416_);
v___x_3418_ = l_Lean_Parser_andthen(v___x_3407_, v___x_3417_);
v___x_3419_ = 0;
v___x_3420_ = l_Lean_Parser_nodeWithAntiquot(v___x_3405_, v___x_3406_, v___x_3418_, v___x_3419_);
v_fn_3421_ = lean_ctor_get(v___x_3420_, 1);
lean_inc_ref(v_fn_3421_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = lean_apply_2(v_fn_3421_, v_a_3403_, v_a_3404_);
return v___x_3422_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6(void){
_start:
{
uint8_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3428_ = 1;
v___x_3429_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5));
v___x_3430_ = ((lean_object*)(l_Lean_Doc_Syntax_block_quot___closed__0));
v___x_3431_ = l_Lean_Parser_mkAntiquot(v___x_3430_, v___x_3429_, v___x_3428_, v___x_3428_);
return v___x_3431_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_3433_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3432_);
return v___x_3434_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7(void){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_3436_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v___x_3435_);
return v___x_3437_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8);
v___x_3439_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7);
v___x_3440_ = l_Lean_Parser_orelse(v___x_3439_, v___x_3438_);
return v___x_3440_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4(void){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3441_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_3442_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v___x_3441_);
return v___x_3443_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10(void){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3444_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9);
v___x_3445_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4);
v___x_3446_ = l_Lean_Parser_orelse(v___x_3445_, v___x_3444_);
return v___x_3446_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3(void){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3447_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_3448_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
lean_ctor_set(v___x_3449_, 1, v___x_3447_);
return v___x_3449_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10);
v___x_3451_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3);
v___x_3452_ = l_Lean_Parser_orelse(v___x_3451_, v___x_3450_);
return v___x_3452_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_3454_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3454_);
lean_ctor_set(v___x_3455_, 1, v___x_3453_);
return v___x_3455_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12(void){
_start:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11);
v___x_3457_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2);
v___x_3458_ = l_Lean_Parser_orelse(v___x_3457_, v___x_3456_);
return v___x_3458_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1(void){
_start:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3459_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_3460_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
lean_ctor_set(v___x_3461_, 1, v___x_3459_);
return v___x_3461_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13(void){
_start:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12);
v___x_3463_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1);
v___x_3464_ = l_Lean_Parser_orelse(v___x_3463_, v___x_3462_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object* v_c_3465_, lean_object* v_s_3466_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v_fn_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v_alts_3487_; lean_object* v_fn_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; 
v___x_3467_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3468_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot), 2, 0);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot), 2, 0);
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3467_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot), 2, 0);
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3467_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot), 2, 0);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3467_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0);
v___x_3477_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot), 2, 0);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3467_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6);
v_fn_3480_ = lean_ctor_get(v___x_3479_, 1);
v___x_3481_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13);
v___x_3482_ = l_Lean_Parser_orelse(v___x_3478_, v___x_3481_);
v___x_3483_ = l_Lean_Parser_orelse(v___x_3476_, v___x_3482_);
v___x_3484_ = l_Lean_Parser_orelse(v___x_3475_, v___x_3483_);
v___x_3485_ = l_Lean_Parser_orelse(v___x_3473_, v___x_3484_);
v___x_3486_ = l_Lean_Parser_orelse(v___x_3471_, v___x_3485_);
v_alts_3487_ = l_Lean_Parser_orelse(v___x_3469_, v___x_3486_);
v_fn_3488_ = lean_ctor_get(v_alts_3487_, 1);
lean_inc_ref(v_fn_3488_);
lean_dec_ref(v_alts_3487_);
v___x_3489_ = 0;
lean_inc_ref(v_fn_3480_);
v___x_3490_ = l_Lean_Parser_withAntiquotFn(v_fn_3480_, v_fn_3488_, v___x_3489_, v_c_3465_, v_s_3466_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; lean_object* v___x_3505_; lean_object* v_fn_3506_; lean_object* v___x_3507_; 
v___x_3493_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0));
v___x_3494_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_3495_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker;
v___x_3496_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3497_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5);
v___x_3498_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3496_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_Parser_atomic(v___x_3499_);
v___x_3501_ = l_Lean_Parser_many(v___x_3500_);
v___x_3502_ = l_Lean_Parser_andthen(v___x_3497_, v___x_3501_);
v___x_3503_ = l_Lean_Parser_andthen(v___x_3495_, v___x_3502_);
v___x_3504_ = 0;
v___x_3505_ = l_Lean_Parser_nodeWithAntiquot(v___x_3493_, v___x_3494_, v___x_3503_, v___x_3504_);
v_fn_3506_ = lean_ctor_get(v___x_3505_, 1);
lean_inc_ref(v_fn_3506_);
lean_dec_ref(v___x_3505_);
v___x_3507_ = lean_apply_2(v_fn_3506_, v_a_3491_, v_a_3492_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object* v_a_3508_, lean_object* v_a_3509_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; lean_object* v___x_3518_; lean_object* v_fn_3519_; lean_object* v___x_3520_; 
v___x_3510_ = ((lean_object*)(l_Lean_Doc_Syntax_dl___closed__0));
v___x_3511_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_3512_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3513_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot), 2, 0);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = l_Lean_Parser_atomic(v___x_3514_);
v___x_3516_ = l_Lean_Parser_many1(v___x_3515_);
v___x_3517_ = 0;
v___x_3518_ = l_Lean_Parser_nodeWithAntiquot(v___x_3510_, v___x_3511_, v___x_3516_, v___x_3517_);
v_fn_3519_ = lean_ctor_get(v___x_3518_, 1);
lean_inc_ref(v_fn_3519_);
lean_dec_ref(v___x_3518_);
v___x_3520_ = lean_apply_2(v_fn_3519_, v_a_3508_, v_a_3509_);
return v___x_3520_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ListItem_item___closed__0(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = l_Lean_Doc_Parser_listMarker;
v___x_3522_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3522_, 0, v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ListItem_item___closed__1(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3523_ = lean_obj_once(&l_Lean_Doc_Parser_ListItem_item___closed__0, &l_Lean_Doc_Parser_ListItem_item___closed__0_once, _init_l_Lean_Doc_Parser_ListItem_item___closed__0);
v___x_3524_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v___x_3523_);
return v___x_3525_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ListItem_item(void){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = lean_obj_once(&l_Lean_Doc_Parser_ListItem_item___closed__1, &l_Lean_Doc_Parser_ListItem_item___closed__1_once, _init_l_Lean_Doc_Parser_ListItem_item___closed__1);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1(){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_3529_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0));
v___x_3530_ = l_Lean_addBuiltinDocString(v___x_3528_, v___x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1(){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_3540_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0));
v___x_3541_ = l_Lean_addBuiltinDocString(v___x_3539_, v___x_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
return v_res_3543_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para___closed__0(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_3545_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v___x_3544_);
return v___x_3546_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para(void){
_start:
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_obj_once(&l_Lean_Doc_Parser_Block_para___closed__0, &l_Lean_Doc_Parser_Block_para___closed__0_once, _init_l_Lean_Doc_Parser_Block_para___closed__0);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1(){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3549_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1));
v___x_3550_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0));
v___x_3551_ = l_Lean_addBuiltinDocString(v___x_3549_, v___x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object* v_a_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1(){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_3561_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0));
v___x_3562_ = l_Lean_addBuiltinDocString(v___x_3560_, v___x_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object* v_a_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1(){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_3572_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0));
v___x_3573_ = l_Lean_addBuiltinDocString(v___x_3571_, v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1(){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_3583_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0));
v___x_3584_ = l_Lean_addBuiltinDocString(v___x_3582_, v___x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1(){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_3594_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0));
v___x_3595_ = l_Lean_addBuiltinDocString(v___x_3593_, v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
return v_res_3597_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock___closed__0(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_3599_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___x_3598_);
return v___x_3600_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock(void){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = lean_obj_once(&l_Lean_Doc_Parser_Block_codeblock___closed__0, &l_Lean_Doc_Parser_Block_codeblock___closed__0_once, _init_l_Lean_Doc_Parser_Block_codeblock___closed__0);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1(){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3603_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_3604_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0));
v___x_3605_ = l_Lean_addBuiltinDocString(v___x_3603_, v___x_3604_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object* v_a_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1(){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_3615_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0));
v___x_3616_ = l_Lean_addBuiltinDocString(v___x_3614_, v___x_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object* v_a_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
return v_res_3618_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header___closed__0(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_3620_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___x_3619_);
return v___x_3621_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header(void){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = lean_obj_once(&l_Lean_Doc_Parser_Block_header___closed__0, &l_Lean_Doc_Parser_Block_header___closed__0_once, _init_l_Lean_Doc_Parser_Block_header___closed__0);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1(){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3624_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_3625_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0));
v___x_3626_ = l_Lean_addBuiltinDocString(v___x_3624_, v___x_3625_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
return v_res_3628_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref___closed__0(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_3630_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
lean_ctor_set(v___x_3631_, 1, v___x_3629_);
return v___x_3631_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref(void){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = lean_obj_once(&l_Lean_Doc_Parser_Block_link__ref___closed__0, &l_Lean_Doc_Parser_Block_link__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_link__ref___closed__0);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1(){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_3635_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0));
v___x_3636_ = l_Lean_addBuiltinDocString(v___x_3634_, v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
return v_res_3638_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_3640_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
lean_ctor_set(v___x_3641_, 1, v___x_3639_);
return v___x_3641_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref(void){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = lean_obj_once(&l_Lean_Doc_Parser_Block_footnote__ref___closed__0, &l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1(){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_3645_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0));
v___x_3646_ = l_Lean_addBuiltinDocString(v___x_3644_, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
return v_res_3648_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3649_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_3650_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
lean_ctor_set(v___x_3651_, 1, v___x_3649_);
return v___x_3651_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block(void){
_start:
{
lean_object* v___x_3652_; 
v___x_3652_ = lean_obj_once(&l_Lean_Doc_Parser_Block_metadata__block___closed__0, &l_Lean_Doc_Parser_Block_metadata__block___closed__0_once, _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1(){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3654_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_3655_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0));
v___x_3656_ = l_Lean_addBuiltinDocString(v___x_3654_, v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object* v_a_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
return v_res_3658_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command___closed__0(void){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_3660_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__3));
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___x_3659_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command(void){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_obj_once(&l_Lean_Doc_Parser_Block_command___closed__0, &l_Lean_Doc_Parser_Block_command___closed__0_once, _init_l_Lean_Doc_Parser_Block_command___closed__0);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1(){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_3665_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0));
v___x_3666_ = l_Lean_addBuiltinDocString(v___x_3664_, v___x_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object* v_a_3667_){
_start:
{
lean_object* v_res_3668_; 
v_res_3668_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
return v_res_3668_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___closed__2(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = ((lean_object*)(l_Lean_Doc_Parser_block));
v___x_3681_ = l_Lean_Parser_atomic(v___x_3680_);
return v___x_3681_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___closed__3(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = lean_obj_once(&l_Lean_Doc_Parser_document___closed__2, &l_Lean_Doc_Parser_document___closed__2_once, _init_l_Lean_Doc_Parser_document___closed__2);
v___x_3683_ = l_Lean_Parser_many(v___x_3682_);
return v___x_3683_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___closed__4(void){
_start:
{
uint8_t v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3684_ = 0;
v___x_3685_ = lean_obj_once(&l_Lean_Doc_Parser_document___closed__3, &l_Lean_Doc_Parser_document___closed__3_once, _init_l_Lean_Doc_Parser_document___closed__3);
v___x_3686_ = ((lean_object*)(l_Lean_Doc_Parser_document___closed__1));
v___x_3687_ = ((lean_object*)(l_Lean_Doc_Parser_document___closed__0));
v___x_3688_ = l_Lean_Parser_nodeWithAntiquot(v___x_3687_, v___x_3686_, v___x_3685_, v___x_3684_);
return v___x_3688_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document(void){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_obj_once(&l_Lean_Doc_Parser_document___closed__4, &l_Lean_Doc_Parser_document___closed__4_once, _init_l_Lean_Doc_Parser_document___closed__4);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(size_t v_sz_3690_, size_t v_i_3691_, lean_object* v_bs_3692_){
_start:
{
uint8_t v___x_3693_; 
v___x_3693_ = lean_usize_dec_lt(v_i_3691_, v_sz_3690_);
if (v___x_3693_ == 0)
{
return v_bs_3692_;
}
else
{
lean_object* v_v_3694_; lean_object* v___x_3695_; lean_object* v_bs_x27_3696_; size_t v___x_3697_; size_t v___x_3698_; lean_object* v___x_3699_; 
v_v_3694_ = lean_array_uget(v_bs_3692_, v_i_3691_);
v___x_3695_ = lean_unsigned_to_nat(0u);
v_bs_x27_3696_ = lean_array_uset(v_bs_3692_, v_i_3691_, v___x_3695_);
v___x_3697_ = ((size_t)1ULL);
v___x_3698_ = lean_usize_add(v_i_3691_, v___x_3697_);
v___x_3699_ = lean_array_uset(v_bs_x27_3696_, v_i_3691_, v_v_3694_);
v_i_3691_ = v___x_3698_;
v_bs_3692_ = v___x_3699_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0___boxed(lean_object* v_sz_3701_, lean_object* v_i_3702_, lean_object* v_bs_3703_){
_start:
{
size_t v_sz_boxed_3704_; size_t v_i_boxed_3705_; lean_object* v_res_3706_; 
v_sz_boxed_3704_ = lean_unbox_usize(v_sz_3701_);
lean_dec(v_sz_3701_);
v_i_boxed_3705_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_res_3706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_boxed_3704_, v_i_boxed_3705_, v_bs_3703_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object* v_doc_3707_){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; size_t v_sz_3711_; size_t v___x_3712_; lean_object* v___x_3713_; 
v___x_3708_ = lean_unsigned_to_nat(0u);
v___x_3709_ = l_Lean_Syntax_getArg(v_doc_3707_, v___x_3708_);
v___x_3710_ = l_Lean_Syntax_getArgs(v___x_3709_);
lean_dec(v___x_3709_);
v_sz_3711_ = lean_array_size(v___x_3710_);
v___x_3712_ = ((size_t)0ULL);
v___x_3713_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_3711_, v___x_3712_, v___x_3710_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks___boxed(lean_object* v_doc_3714_){
_start:
{
lean_object* v_res_3715_; 
v_res_3715_ = l_Lean_TSyntax_getVersoBlocks(v_doc_3714_);
lean_dec(v_doc_3714_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object* v_delim_3716_){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_unsigned_to_nat(0u);
v___x_3718_ = l_Lean_Syntax_getArg(v_delim_3716_, v___x_3717_);
v___x_3719_ = l_Lean_Syntax_getAtomVal(v___x_3718_);
lean_dec(v___x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter___boxed(lean_object* v_delim_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_3720_);
lean_dec(v_delim_3720_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(lean_object* v_s_3724_){
_start:
{
lean_inc(v_s_3724_);
return v_s_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed(lean_object* v_s_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(v_s_3725_);
lean_dec(v_s_3725_);
return v_res_3726_;
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
l_Lean_Doc_Parser_versoCodeLine = _init_l_Lean_Doc_Parser_versoCodeLine();
lean_mark_persistent(l_Lean_Doc_Parser_versoCodeLine);
l_Lean_Doc_Parser_versoCodeBlock = _init_l_Lean_Doc_Parser_versoCodeBlock();
lean_mark_persistent(l_Lean_Doc_Parser_versoCodeBlock);
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

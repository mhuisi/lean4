// Lean compiler output
// Module: Lean.DocString.View
// Imports: public import Lean.DocString.Types public import Lean.Parser.Term.Basic public import Lean.DocString.Syntax meta import Lean.DocString.Syntax
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
lean_object* l_Lean_TSyntax_getVersoRefName(lean_object*);
extern lean_object* l_Lean_Doc_versoCodeKind;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Doc_versoCodeBlockLineKind;
extern lean_object* l_Lean_Doc_versoCodeBlockKind;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Doc_versoLinkRefUrlKind;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
extern lean_object* l_Lean_Doc_versoRefKind;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
extern lean_object* l_Lean_Doc_versoImageAltKind;
lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
extern lean_object* l_Lean_Doc_versoLinkUrlKind;
lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object*);
lean_object* l_Lean_Doc_longestBacktickRun(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_Lean_Doc_versoTextKind;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_TSyntax_getNat(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object*);
lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object*);
lean_object* l_Lean_TSyntax_getVersoText(lean_object*);
lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__2 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ArgVal"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__3 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__4 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__4_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value_aux_3),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 191, 138, 67, 72, 90, 15, 127)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__5 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__5_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__6 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__6_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_2),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value_aux_3),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__6_value),LEAN_SCALAR_PTR_LITERAL(233, 188, 228, 197, 246, 25, 189, 153)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__7 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__7_value;
static const lean_string_object l_Lean_Doc_ArgValView_of___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__8 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__8_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_2),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value_aux_3),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 66, 72, 255, 161, 123, 180, 197)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__9 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__9_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__8_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__10 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__10_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__6_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__11 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__11_value;
static const lean_ctor_object l_Lean_Doc_ArgValView_of___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Doc_ArgValView_of___closed__12 = (const lean_object*)&l_Lean_Doc_ArgValView_of___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_ArgView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Arg"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "anon"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__1_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(108, 126, 223, 228, 215, 141, 22, 177)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__2 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__2_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__3 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__3_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 213, 136, 95, 26, 15, 91, 243)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__4 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__4_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "named_no_paren"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__5 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__5_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 130, 4, 13, 153, 240, 131, 1)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__6 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__6_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flag_on"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__7 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__7_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__7_value),LEAN_SCALAR_PTR_LITERAL(199, 11, 92, 179, 92, 210, 69, 32)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__8 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__8_value;
static const lean_string_object l_Lean_Doc_ArgView_of___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "flag_off"};
static const lean_object* l_Lean_Doc_ArgView_of___closed__9 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__9_value;
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_ArgView_of___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value_aux_3),((lean_object*)&l_Lean_Doc_ArgView_of___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 14, 2, 143, 165, 169, 65, 229)}};
static const lean_object* l_Lean_Doc_ArgView_of___closed__10 = (const lean_object*)&l_Lean_Doc_ArgView_of___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "codeDelimiter"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 116, 135, 82, 225, 37, 203, 104)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1_value;
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "codeBlockFence"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 154, 39, 84, 226, 168, 56, 199)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1_value;
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "```"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "directiveDelimiter"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 28, 38, 38, 72, 11, 173, 25)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1_value;
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ":::"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\\\\"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_mkVersoCodeFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Doc_mkVersoCodeFrom___closed__0 = (const lean_object*)&l_Lean_Doc_mkVersoCodeFrom___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_mkVersoCodeBlockFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___closed__0 = (const lean_object*)&l_Lean_Doc_mkVersoCodeBlockFrom___closed__0_value;
static const lean_ctor_object l_Lean_Doc_mkVersoCodeBlockFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_mkVersoCodeBlockFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___closed__1 = (const lean_object*)&l_Lean_Doc_mkVersoCodeBlockFrom___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Inline"};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__0 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value;
static const lean_string_object l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__1 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value;
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(175, 150, 35, 119, 78, 160, 253, 84)}};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__2 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__2_value;
static const lean_string_object l_Lean_Doc_mkVersoLinebreakFrom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Doc_mkVersoLinebreakFrom___closed__3 = (const lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asNode(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_argValToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Doc_argValToParser___closed__0 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__0_value;
static const lean_string_object l_Lean_Doc_argValToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arg_ident"};
static const lean_object* l_Lean_Doc_argValToParser___closed__1 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__1_value;
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_argValToParser___closed__1_value),LEAN_SCALAR_PTR_LITERAL(73, 49, 249, 222, 84, 35, 6, 34)}};
static const lean_object* l_Lean_Doc_argValToParser___closed__2 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__2_value;
static const lean_string_object l_Lean_Doc_argValToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_num"};
static const lean_object* l_Lean_Doc_argValToParser___closed__3 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__3_value;
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_argValToParser___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 247, 226, 130, 46, 200, 13, 201)}};
static const lean_object* l_Lean_Doc_argValToParser___closed__4 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__4_value;
static const lean_string_object l_Lean_Doc_argValToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_str"};
static const lean_object* l_Lean_Doc_argValToParser___closed__5 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_argValToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_argValToParser___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_argValToParser___closed__5_value),LEAN_SCALAR_PTR_LITERAL(28, 110, 66, 227, 168, 59, 232, 226)}};
static const lean_object* l_Lean_Doc_argValToParser___closed__6 = (const lean_object*)&l_Lean_Doc_argValToParser___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_argValToParser(lean_object*);
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(151, 30, 185, 65, 40, 8, 94, 56)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__0 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__3_value),LEAN_SCALAR_PTR_LITERAL(240, 209, 4, 173, 176, 102, 100, 110)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__1 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__1_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 78, 240, 214, 103, 62, 217, 25)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__2 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__7_value),LEAN_SCALAR_PTR_LITERAL(156, 222, 140, 123, 199, 224, 2, 54)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__3 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__3_value;
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_docArgToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_ArgView_of___closed__9_value),LEAN_SCALAR_PTR_LITERAL(29, 0, 37, 229, 12, 38, 20, 228)}};
static const lean_object* l_Lean_Doc_docArgToParser___closed__4 = (const lean_object*)&l_Lean_Doc_docArgToParser___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Doc_docArgToParser(lean_object*);
static const lean_string_object l_Lean_Doc_linkTargetToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__0 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 109, 202, 165, 136, 148, 125, 206)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__1 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_linkTargetToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__2 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(157, 197, 143, 220, 44, 158, 31, 133)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__3 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_linkTargetToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LinkTarget"};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__4 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__4_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value_aux_3),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 54, 241, 38, 78, 206, 156, 5)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__5 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_linkTargetToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value_aux_3),((lean_object*)&l_Lean_Doc_linkTargetToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 147, 211, 241, 202, 7, 251)}};
static const lean_object* l_Lean_Doc_linkTargetToParser___closed__6 = (const lean_object*)&l_Lean_Doc_linkTargetToParser___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_linkTargetToParser(lean_object*);
static const lean_string_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 30, 73, 79, 76, 254, 8, 196)}};
static const lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1 = (const lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_inlineToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__0 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 149, 124, 218, 116, 154, 240, 105)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__1 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__2 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 183, 215, 94, 0, 242, 191, 239)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__3 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__4 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__4_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(217, 240, 207, 144, 35, 3, 119, 11)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__5 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value_aux_2),((lean_object*)&l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 172, 118, 77, 213, 142, 126)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__6 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__6_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__7 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__7_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__7_value),LEAN_SCALAR_PTR_LITERAL(39, 58, 152, 4, 55, 96, 114, 182)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__8 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__8_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__9 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__9_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__9_value),LEAN_SCALAR_PTR_LITERAL(185, 134, 189, 58, 202, 192, 153, 244)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__10 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__10_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__11 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__11_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__11_value),LEAN_SCALAR_PTR_LITERAL(129, 184, 35, 28, 112, 167, 76, 80)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__12 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__12_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__13 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__13_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__13_value),LEAN_SCALAR_PTR_LITERAL(156, 113, 65, 80, 13, 110, 129, 61)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__14 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__14_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__15 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__15_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__15_value),LEAN_SCALAR_PTR_LITERAL(207, 87, 199, 0, 139, 133, 244, 123)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__16 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__16_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 183, 85, 224, 226, 177, 67, 207)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__17 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__17_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__18 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__18_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(88, 39, 13, 65, 153, 69, 141, 111)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__19 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__19_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(163, 233, 178, 241, 96, 238, 218, 92)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__20 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__20_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__21 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__21_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__22 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__22_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Doc_inlineToParser___closed__23 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__23_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__24 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__24_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__15_value),LEAN_SCALAR_PTR_LITERAL(44, 121, 147, 210, 143, 103, 0, 217)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__25 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__25_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__26 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__26_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__13_value),LEAN_SCALAR_PTR_LITERAL(63, 170, 102, 209, 119, 14, 254, 233)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__27 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__27_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l_Lean_Doc_inlineToParser___closed__28 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__28_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__11_value),LEAN_SCALAR_PTR_LITERAL(250, 237, 8, 103, 58, 149, 183, 251)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__29 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__29_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__9_value),LEAN_SCALAR_PTR_LITERAL(194, 39, 73, 53, 10, 24, 181, 77)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__30 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__30_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "displayMathMarker"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__31 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__31_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__31_value),LEAN_SCALAR_PTR_LITERAL(191, 18, 116, 40, 86, 165, 207, 150)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__32 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__32_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__33 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__33_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 236, 9, 179, 133, 206, 252, 7)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__34 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__34_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inlineMathMarker"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__35 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__35_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__35_value),LEAN_SCALAR_PTR_LITERAL(102, 9, 108, 134, 130, 7, 90, 114)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__36 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__36_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__37 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__37_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 21, 54, 220, 135, 144, 211, 134)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__38 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__38_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "boldDelimiter"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__39 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__39_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__39_value),LEAN_SCALAR_PTR_LITERAL(187, 9, 73, 54, 22, 222, 115, 214)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__40 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__40_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__41 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__41_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 215, 18, 85, 144, 91, 153, 50)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__42 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__42_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "emphDelimiter"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__43 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__43_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value_aux_2),((lean_object*)&l_Lean_Doc_inlineToParser___closed__43_value),LEAN_SCALAR_PTR_LITERAL(14, 57, 61, 189, 31, 180, 10, 101)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__44 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__44_value;
static const lean_string_object l_Lean_Doc_inlineToParser___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Doc_inlineToParser___closed__45 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__45_value;
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_2),((lean_object*)&l_Lean_Doc_mkVersoLinebreakFrom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l_Lean_Doc_inlineToParser___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value_aux_3),((lean_object*)&l_Lean_Doc_inlineToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 133, 107, 199, 31, 216, 160, 200)}};
static const lean_object* l_Lean_Doc_inlineToParser___closed__46 = (const lean_object*)&l_Lean_Doc_inlineToParser___closed__46_value;
LEAN_EXPORT lean_object* l_Lean_Doc_inlineToParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_blockToParser_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_blockToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l_Lean_Doc_blockToParser___closed__0 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 72, 198, 245, 142, 145, 171, 144)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__1 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l_Lean_Doc_blockToParser___closed__2 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(154, 37, 74, 205, 107, 38, 107, 223)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__3 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l_Lean_Doc_blockToParser___closed__4 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__4_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(248, 90, 162, 51, 92, 30, 144, 89)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__5 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__5_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l_Lean_Doc_blockToParser___closed__6 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__6_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__7_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__7_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__7_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 73, 192, 118, 161, 88, 51, 173)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__7 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__7_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l_Lean_Doc_blockToParser___closed__8 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__8_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__9_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__9_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__9_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__8_value),LEAN_SCALAR_PTR_LITERAL(13, 49, 30, 64, 139, 101, 177, 168)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__9 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__9_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l_Lean_Doc_blockToParser___closed__10 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__10_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__11_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__11_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__11_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__10_value),LEAN_SCALAR_PTR_LITERAL(228, 242, 241, 127, 13, 6, 27, 177)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__11 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__11_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l_Lean_Doc_blockToParser___closed__12 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__12_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__13_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__13_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__13_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__12_value),LEAN_SCALAR_PTR_LITERAL(59, 236, 126, 236, 245, 181, 4, 182)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__13 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__13_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Doc_blockToParser___closed__14 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__14_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__15_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__15_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__15_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__14_value),LEAN_SCALAR_PTR_LITERAL(163, 102, 246, 27, 44, 229, 232, 70)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__15 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__15_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Doc_blockToParser___closed__16 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__16_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__17_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__17_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__17_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__16_value),LEAN_SCALAR_PTR_LITERAL(138, 131, 27, 234, 140, 72, 2, 168)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__17 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__17_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "link_ref"};
static const lean_object* l_Lean_Doc_blockToParser___closed__18 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__18_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__19_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__19_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__19_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(37, 122, 52, 169, 192, 153, 29, 165)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__19 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__19_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "footnote_ref"};
static const lean_object* l_Lean_Doc_blockToParser___closed__20 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__20_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__21_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__21_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__21_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__20_value),LEAN_SCALAR_PTR_LITERAL(249, 7, 163, 121, 208, 236, 208, 13)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__21 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__21_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l_Lean_Doc_blockToParser___closed__22 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__22_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__23_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__23_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__23_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 201, 5, 85, 129, 97, 253, 216)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__23 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__23_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l_Lean_Doc_blockToParser___closed__25 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__25_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Doc_blockToParser___closed__24 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__24_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__26_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__26_value_aux_1),((lean_object*)&l_Lean_Doc_blockToParser___closed__24_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__26_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__25_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__26 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__26_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Block"};
static const lean_object* l_Lean_Doc_blockToParser___closed__27 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__27_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__28_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__22_value),LEAN_SCALAR_PTR_LITERAL(99, 125, 116, 48, 167, 45, 110, 42)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__28 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__28_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__29_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__20_value),LEAN_SCALAR_PTR_LITERAL(97, 53, 29, 246, 154, 171, 121, 154)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__29 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__29_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__30_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__18_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 233, 128, 119, 237, 18, 215)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__30 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__30_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__31_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__16_value),LEAN_SCALAR_PTR_LITERAL(242, 176, 128, 73, 36, 235, 244, 141)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__31 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__31_value;
static const lean_string_object l_Lean_Doc_blockToParser___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "headerMarker"};
static const lean_object* l_Lean_Doc_blockToParser___closed__32 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__32_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__33_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__33_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__33_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__32_value),LEAN_SCALAR_PTR_LITERAL(79, 163, 210, 90, 152, 248, 144, 166)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__33 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__33_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__34_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__14_value),LEAN_SCALAR_PTR_LITERAL(11, 232, 253, 29, 141, 75, 139, 21)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__34 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__34_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__35_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__12_value),LEAN_SCALAR_PTR_LITERAL(211, 234, 1, 42, 159, 198, 19, 176)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__35 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__35_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__36_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__10_value),LEAN_SCALAR_PTR_LITERAL(76, 32, 43, 99, 217, 167, 97, 87)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__36 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__36_value;
static const lean_array_object l_Lean_Doc_blockToParser___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Doc_blockToParser___closed__37 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__37_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Doc_mkVersoCodeBlockFrom___closed__1_value),((lean_object*)&l_Lean_Doc_blockToParser___closed__37_value)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__38 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__38_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__39_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__8_value),LEAN_SCALAR_PTR_LITERAL(165, 15, 76, 66, 114, 120, 124, 74)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__39 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__39_value;
static const lean_string_object l_Lean_Doc_descItemToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l_Lean_Doc_descItemToParser___closed__0 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_descItemToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 44, 92, 80, 93, 40, 168, 47)}};
static const lean_object* l_Lean_Doc_descItemToParser___closed__1 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__3 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__3_value;
static const lean_string_object l_Lean_Doc_descItemToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DescItem"};
static const lean_object* l_Lean_Doc_descItemToParser___closed__2 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_descItemToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 70, 30, 3, 105, 156, 130, 115)}};
static const lean_ctor_object l_Lean_Doc_descItemToParser___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value_aux_3),((lean_object*)&l_Lean_Doc_listItemToParser___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 193, 144, 210, 183, 212, 114, 89)}};
static const lean_object* l_Lean_Doc_descItemToParser___closed__3 = (const lean_object*)&l_Lean_Doc_descItemToParser___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_descItemToParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(size_t, size_t, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "li"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__0 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__0_value;
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_argValToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_listItemToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 229, 0, 156, 136, 247, 163, 99)}};
static const lean_object* l_Lean_Doc_listItemToParser___closed__1 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__1_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ListItem"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__2 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__2_value;
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_listItemToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(154, 153, 101, 209, 126, 16, 11, 208)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value_aux_3),((lean_object*)&l_Lean_Doc_listItemToParser___closed__3_value),LEAN_SCALAR_PTR_LITERAL(200, 123, 16, 134, 76, 179, 171, 228)}};
static const lean_object* l_Lean_Doc_listItemToParser___closed__4 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__4_value;
static const lean_string_object l_Lean_Doc_listItemToParser___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "listMarker"};
static const lean_object* l_Lean_Doc_listItemToParser___closed__5 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__5_value;
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_listItemToParser___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value_aux_2),((lean_object*)&l_Lean_Doc_listItemToParser___closed__5_value),LEAN_SCALAR_PTR_LITERAL(220, 134, 18, 7, 181, 33, 85, 37)}};
static const lean_object* l_Lean_Doc_listItemToParser___closed__6 = (const lean_object*)&l_Lean_Doc_listItemToParser___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Doc_listItemToParser(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(lean_object*, size_t, size_t, lean_object*);
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__40_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__6_value),LEAN_SCALAR_PTR_LITERAL(222, 199, 227, 191, 40, 60, 185, 243)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__40 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__40_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__41_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__4_value),LEAN_SCALAR_PTR_LITERAL(144, 45, 1, 212, 241, 159, 201, 84)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__41 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__41_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(size_t, size_t, lean_object*);
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__42_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__2_value),LEAN_SCALAR_PTR_LITERAL(130, 145, 178, 243, 42, 6, 105, 104)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__42 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__42_value;
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__43_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__43_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__43_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__43_value_aux_2),((lean_object*)&l_Lean_Doc_blockToParser___closed__27_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l_Lean_Doc_blockToParser___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_blockToParser___closed__43_value_aux_3),((lean_object*)&l_Lean_Doc_blockToParser___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 167, 213, 66, 92, 160, 222, 146)}};
static const lean_object* l_Lean_Doc_blockToParser___closed__43 = (const lean_object*)&l_Lean_Doc_blockToParser___closed__43_value;
LEAN_EXPORT lean_object* l_Lean_Doc_blockToParser(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_argValToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_docArgToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_linkTargetToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_inlineToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_descItemToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_blockToParser, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__7_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__2_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__3_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__4_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__8_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value)} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__1_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__3___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value)} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__1___closed__0_value;
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr4__lean__4___closed__0_value),((lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___closed__0_value)} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "versoRef"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__0 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 44, 27, 25, 170, 146, 153, 245)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__1 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__1_value;
static const lean_string_object l_Lean_Doc_LinkTargetView_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "versoLinkUrl"};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__2 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value;
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkTargetView_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 188, 54, 130, 131, 60, 251, 148)}};
static const lean_object* l_Lean_Doc_LinkTargetView_of___closed__3 = (const lean_object*)&l_Lean_Doc_LinkTargetView_of___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_narrowToValue_shrink(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_narrowToValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_TextView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoText"};
static const lean_object* l_Lean_Doc_TextView_of___closed__0 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_TextView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_TextView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_TextView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 255, 240, 17, 75, 250, 253, 95)}};
static const lean_object* l_Lean_Doc_TextView_of___closed__1 = (const lean_object*)&l_Lean_Doc_TextView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_CodeView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoCode"};
static const lean_object* l_Lean_Doc_CodeView_of___closed__0 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_CodeView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 134, 52, 97, 245, 192, 23, 73)}};
static const lean_object* l_Lean_Doc_CodeView_of___closed__1 = (const lean_object*)&l_Lean_Doc_CodeView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_ImageView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "versoImageAlt"};
static const lean_object* l_Lean_Doc_ImageView_of___closed__0 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_ImageView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_ImageView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 180, 119, 241, 128, 95, 219, 17)}};
static const lean_object* l_Lean_Doc_ImageView_of___closed__1 = (const lean_object*)&l_Lean_Doc_ImageView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTextViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTextViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTextViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTextViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTextViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeTextViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeEmphViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeEmphViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeEmphViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeEmphViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeEmphViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeEmphViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeBoldViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeBoldViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeBoldViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeBoldViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeBoldViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeBoldViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeCodeViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeCodeViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeCodeViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeCodeViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeCodeViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeCodeViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeMathViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeMathViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeMathViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeMathViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeMathViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeMathViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeLinkViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeLinkViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeLinkViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeLinkViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeLinkViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeLinkViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeImageViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeImageViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeImageViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeImageViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeImageViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeImageViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeFootnoteViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeLinebreakViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeRoleViewInlineView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeRoleViewInlineView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeRoleViewInlineView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeRoleViewInlineView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeRoleViewInlineView = (const lean_object*)&l_Lean_Doc_instCoeRoleViewInlineView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__1;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_UnorderedListItemView_of___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_UnorderedListItemView_of___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_CodeBlockView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "versoCodeBlock"};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__0 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_CodeBlockView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 196, 91, 225, 102, 151, 154, 53)}};
static const lean_object* l_Lean_Doc_CodeBlockView_of___closed__1 = (const lean_object*)&l_Lean_Doc_CodeBlockView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_LinkRefView_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "versoLinkRefUrl"};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__0 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__0_value;
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_ArgValView_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_LinkRefView_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_LinkRefView_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 57, 106, 22, 121, 78, 15, 41)}};
static const lean_object* l_Lean_Doc_LinkRefView_of___closed__1 = (const lean_object*)&l_Lean_Doc_LinkRefView_of___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeParaViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeParaViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeParaViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeParaViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeParaViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeParaViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeUnorderedListViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeOrderedListViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeDescListViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeDescListViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeDescListViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeDescListViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeDescListViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeDescListViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeBlockquoteViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeCodeBlockViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeDirectiveViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeCommandViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeCommandViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeCommandViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeCommandViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeCommandViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeCommandViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeHeaderViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeHeaderViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeHeaderViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeHeaderViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeHeaderViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeLinkRefViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeFootnoteRefViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeMetadataViewBlockView___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeMetadataViewBlockView___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeMetadataViewBlockView___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeMetadataViewBlockView = (const lean_object*)&l_Lean_Doc_instCoeMetadataViewBlockView___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Doc_ArgValView_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
switch(lean_obj_tag(v_t_7_))
{
case 0:
{
lean_object* v_lit_9_; lean_object* v_value_10_; lean_object* v___x_11_; 
v_lit_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_lit_9_);
v_value_10_ = lean_ctor_get(v_t_7_, 1);
lean_inc_ref(v_value_10_);
lean_dec_ref_known(v_t_7_, 2);
v___x_11_ = lean_apply_2(v_k_8_, v_lit_9_, v_value_10_);
return v___x_11_;
}
case 1:
{
lean_object* v_x_12_; lean_object* v___x_13_; 
v_x_12_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_x_12_);
lean_dec_ref_known(v_t_7_, 1);
v___x_13_ = lean_apply_1(v_k_8_, v_x_12_);
return v___x_13_;
}
default: 
{
lean_object* v_lit_14_; lean_object* v_value_15_; lean_object* v___x_16_; 
v_lit_14_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_lit_14_);
v_value_15_ = lean_ctor_get(v_t_7_, 1);
lean_inc(v_value_15_);
lean_dec_ref_known(v_t_7_, 2);
v___x_16_ = lean_apply_2(v_k_8_, v_lit_14_, v_value_15_);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Doc_ArgValView_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim___redArg(lean_object* v_t_29_, lean_object* v_str_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_29_, v_str_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_str_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_str_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_33_, v_str_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim___redArg(lean_object* v_t_37_, lean_object* v_name_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_37_, v_name_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_name_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_name_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_41_, v_name_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim___redArg(lean_object* v_t_45_, lean_object* v_num_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_45_, v_num_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_num_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_num_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Doc_ArgValView_ctorElim___redArg(v_t_49_, v_num_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgValView_of(lean_object* v_stx_84_){
_start:
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__5));
lean_inc(v_stx_84_);
v___x_86_ = l_Lean_Syntax_isOfKind(v_stx_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__7));
lean_inc(v_stx_84_);
v___x_88_ = l_Lean_Syntax_isOfKind(v_stx_84_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__9));
lean_inc(v_stx_84_);
v___x_90_ = l_Lean_Syntax_isOfKind(v_stx_84_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v_stx_84_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
lean_object* v___x_92_; lean_object* v_s_93_; 
v___x_92_ = lean_unsigned_to_nat(0u);
v_s_93_ = l_Lean_Syntax_getArg(v_stx_84_, v___x_92_);
lean_dec(v_stx_84_);
if (v___x_88_ == 0)
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v_s_93_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_s_93_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec(v_s_93_);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
goto v___jp_94_;
}
}
else
{
goto v___jp_94_;
}
v___jp_94_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = l_Lean_TSyntax_getString(v_s_93_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_s_93_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
}
else
{
lean_object* v___x_101_; lean_object* v_n_102_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v_n_102_ = l_Lean_Syntax_getArg(v_stx_84_, v___x_101_);
lean_dec(v_stx_84_);
if (v___x_86_ == 0)
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__11));
lean_inc(v_n_102_);
v___x_108_ = l_Lean_Syntax_isOfKind(v_n_102_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec(v_n_102_);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
goto v___jp_103_;
}
}
else
{
goto v___jp_103_;
}
v___jp_103_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = l_Lean_TSyntax_getNat(v_n_102_);
v___x_105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_105_, 0, v_n_102_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
}
else
{
lean_object* v___x_110_; lean_object* v_x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v_x_111_ = l_Lean_Syntax_getArg(v_stx_84_, v___x_110_);
lean_dec(v_stx_84_);
v___x_112_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_111_);
v___x_113_ = l_Lean_Syntax_isOfKind(v_x_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
lean_dec(v_x_111_);
v___x_114_ = lean_box(0);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v_x_111_);
v___x_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx(lean_object* v_x_117_){
_start:
{
switch(lean_obj_tag(v_x_117_))
{
case 0:
{
lean_object* v___x_118_; 
v___x_118_ = lean_unsigned_to_nat(0u);
return v___x_118_;
}
case 1:
{
lean_object* v___x_119_; 
v___x_119_ = lean_unsigned_to_nat(1u);
return v___x_119_;
}
default: 
{
lean_object* v___x_120_; 
v___x_120_ = lean_unsigned_to_nat(2u);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorIdx___boxed(lean_object* v_x_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Doc_ArgView_ctorIdx(v_x_121_);
lean_dec_ref(v_x_121_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___redArg(lean_object* v_t_123_, lean_object* v_k_124_){
_start:
{
switch(lean_obj_tag(v_t_123_))
{
case 0:
{
lean_object* v_stx_125_; lean_object* v_val_126_; lean_object* v___x_127_; 
v_stx_125_ = lean_ctor_get(v_t_123_, 0);
lean_inc(v_stx_125_);
v_val_126_ = lean_ctor_get(v_t_123_, 1);
lean_inc(v_val_126_);
lean_dec_ref_known(v_t_123_, 2);
v___x_127_ = lean_apply_2(v_k_124_, v_stx_125_, v_val_126_);
return v___x_127_;
}
case 1:
{
lean_object* v_stx_128_; lean_object* v_parens_129_; lean_object* v_name_130_; lean_object* v_assign_131_; lean_object* v_val_132_; lean_object* v___x_133_; 
v_stx_128_ = lean_ctor_get(v_t_123_, 0);
lean_inc(v_stx_128_);
v_parens_129_ = lean_ctor_get(v_t_123_, 1);
lean_inc(v_parens_129_);
v_name_130_ = lean_ctor_get(v_t_123_, 2);
lean_inc(v_name_130_);
v_assign_131_ = lean_ctor_get(v_t_123_, 3);
lean_inc(v_assign_131_);
v_val_132_ = lean_ctor_get(v_t_123_, 4);
lean_inc(v_val_132_);
lean_dec_ref_known(v_t_123_, 5);
v___x_133_ = lean_apply_5(v_k_124_, v_stx_128_, v_parens_129_, v_name_130_, v_assign_131_, v_val_132_);
return v___x_133_;
}
default: 
{
lean_object* v_stx_134_; lean_object* v_sign_135_; lean_object* v_name_136_; uint8_t v_isOn_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_stx_134_ = lean_ctor_get(v_t_123_, 0);
lean_inc(v_stx_134_);
v_sign_135_ = lean_ctor_get(v_t_123_, 1);
lean_inc(v_sign_135_);
v_name_136_ = lean_ctor_get(v_t_123_, 2);
lean_inc(v_name_136_);
v_isOn_137_ = lean_ctor_get_uint8(v_t_123_, sizeof(void*)*3);
lean_dec_ref_known(v_t_123_, 3);
v___x_138_ = lean_box(v_isOn_137_);
v___x_139_ = lean_apply_4(v_k_124_, v_stx_134_, v_sign_135_, v_name_136_, v___x_138_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim(lean_object* v_motive_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_142_, v_k_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_ctorElim___boxed(lean_object* v_motive_146_, lean_object* v_ctorIdx_147_, lean_object* v_t_148_, lean_object* v_h_149_, lean_object* v_k_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Doc_ArgView_ctorElim(v_motive_146_, v_ctorIdx_147_, v_t_148_, v_h_149_, v_k_150_);
lean_dec(v_ctorIdx_147_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim___redArg(lean_object* v_t_152_, lean_object* v_anon_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_152_, v_anon_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_anon_elim(lean_object* v_motive_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_anon_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_156_, v_anon_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim___redArg(lean_object* v_t_160_, lean_object* v_named_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_160_, v_named_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_named_elim(lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_named_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_164_, v_named_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim___redArg(lean_object* v_t_168_, lean_object* v_flag_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_168_, v_flag_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_flag_elim(lean_object* v_motive_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_flag_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Doc_ArgView_ctorElim___redArg(v_t_172_, v_flag_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx(lean_object* v_x_176_){
_start:
{
lean_object* v_stx_177_; 
v_stx_177_ = lean_ctor_get(v_x_176_, 0);
lean_inc(v_stx_177_);
return v_stx_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_stx___boxed(lean_object* v_x_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Doc_ArgView_stx(v_x_178_);
lean_dec_ref(v_x_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ArgView_of(lean_object* v_stx_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__2));
lean_inc(v_stx_216_);
v___x_218_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__4));
lean_inc(v_stx_216_);
v___x_220_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__6));
lean_inc(v_stx_216_);
v___x_222_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__8));
lean_inc(v_stx_216_);
v___x_224_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__10));
lean_inc(v_stx_216_);
v___x_226_ = l_Lean_Syntax_isOfKind(v_stx_216_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec(v_stx_216_);
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v_tk_229_; lean_object* v___x_230_; lean_object* v_x_231_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v_tk_229_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(1u);
v_x_231_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_230_);
if (v___x_224_ == 0)
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_231_);
v___x_236_ = l_Lean_Syntax_isOfKind(v_x_231_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v_x_231_);
lean_dec(v_tk_229_);
lean_dec(v_stx_216_);
v___x_237_ = lean_box(0);
return v___x_237_;
}
else
{
goto v___jp_232_;
}
}
else
{
goto v___jp_232_;
}
v___jp_232_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_233_, 0, v_stx_216_);
lean_ctor_set(v___x_233_, 1, v_tk_229_);
lean_ctor_set(v___x_233_, 2, v_x_231_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*3, v___x_224_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
}
}
else
{
lean_object* v___x_238_; lean_object* v_tk_239_; lean_object* v___x_240_; lean_object* v_x_241_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v_tk_239_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_238_);
v___x_240_ = lean_unsigned_to_nat(1u);
v_x_241_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_240_);
if (v___x_222_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_241_);
v___x_246_ = l_Lean_Syntax_isOfKind(v_x_241_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
lean_dec(v_x_241_);
lean_dec(v_tk_239_);
lean_dec(v_stx_216_);
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
goto v___jp_242_;
}
}
else
{
goto v___jp_242_;
}
v___jp_242_:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(v___x_243_, 0, v_stx_216_);
lean_ctor_set(v___x_243_, 1, v_tk_239_);
lean_ctor_set(v___x_243_, 2, v_x_241_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*3, v___x_224_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
}
}
else
{
lean_object* v___x_248_; lean_object* v_x_249_; 
v___x_248_ = lean_unsigned_to_nat(0u);
v_x_249_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_248_);
if (v___x_220_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_249_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_249_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec(v_x_249_);
lean_dec(v_stx_216_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
else
{
goto v___jp_250_;
}
}
else
{
goto v___jp_250_;
}
v___jp_250_:
{
lean_object* v___x_251_; lean_object* v_eq_252_; lean_object* v___x_253_; lean_object* v_v_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_251_ = lean_unsigned_to_nat(1u);
v_eq_252_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_251_);
v___x_253_ = lean_unsigned_to_nat(2u);
v_v_254_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_253_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_256_, 0, v_stx_216_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_ctor_set(v___x_256_, 2, v_x_249_);
lean_ctor_set(v___x_256_, 3, v_eq_252_);
lean_ctor_set(v___x_256_, 4, v_v_254_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
else
{
lean_object* v___x_261_; lean_object* v_po_262_; lean_object* v___x_263_; lean_object* v_x_264_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v_po_262_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(1u);
v_x_264_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_263_);
if (v___x_218_ == 0)
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_x_264_);
v___x_277_ = l_Lean_Syntax_isOfKind(v_x_264_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec(v_x_264_);
lean_dec(v_po_262_);
lean_dec(v_stx_216_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
goto v___jp_265_;
}
}
else
{
goto v___jp_265_;
}
v___jp_265_:
{
lean_object* v___x_266_; lean_object* v_eq_267_; lean_object* v___x_268_; lean_object* v_v_269_; lean_object* v___x_270_; lean_object* v_pc_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_266_ = lean_unsigned_to_nat(2u);
v_eq_267_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_266_);
v___x_268_ = lean_unsigned_to_nat(3u);
v_v_269_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(4u);
v_pc_271_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_270_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_po_262_);
lean_ctor_set(v___x_272_, 1, v_pc_271_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
v___x_274_ = lean_alloc_ctor(1, 5, 0);
lean_ctor_set(v___x_274_, 0, v_stx_216_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
lean_ctor_set(v___x_274_, 2, v_x_264_);
lean_ctor_set(v___x_274_, 3, v_eq_267_);
lean_ctor_set(v___x_274_, 4, v_v_269_);
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v_v_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_279_ = lean_unsigned_to_nat(0u);
v_v_280_ = l_Lean_Syntax_getArg(v_stx_216_, v___x_279_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_stx_216_);
lean_ctor_set(v___x_281_, 1, v_v_280_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx(lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_unsigned_to_nat(0u);
return v___x_284_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = lean_unsigned_to_nat(1u);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorIdx___boxed(lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Doc_LinkTargetView_ctorIdx(v_x_286_);
lean_dec_ref(v_x_286_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___redArg(lean_object* v_t_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_stx_290_; lean_object* v_opener_291_; lean_object* v_url_292_; lean_object* v_closer_293_; lean_object* v___x_294_; 
v_stx_290_ = lean_ctor_get(v_t_288_, 0);
lean_inc(v_stx_290_);
v_opener_291_ = lean_ctor_get(v_t_288_, 1);
lean_inc(v_opener_291_);
v_url_292_ = lean_ctor_get(v_t_288_, 2);
lean_inc(v_url_292_);
v_closer_293_ = lean_ctor_get(v_t_288_, 3);
lean_inc(v_closer_293_);
lean_dec_ref(v_t_288_);
v___x_294_ = lean_apply_4(v_k_289_, v_stx_290_, v_opener_291_, v_url_292_, v_closer_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim(lean_object* v_motive_295_, lean_object* v_ctorIdx_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_k_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_297_, v_k_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ctorElim___boxed(lean_object* v_motive_301_, lean_object* v_ctorIdx_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_k_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Doc_LinkTargetView_ctorElim(v_motive_301_, v_ctorIdx_302_, v_t_303_, v_h_304_, v_k_305_);
lean_dec(v_ctorIdx_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim___redArg(lean_object* v_t_307_, lean_object* v_url_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_307_, v_url_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_url_elim(lean_object* v_motive_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_url_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_311_, v_url_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim___redArg(lean_object* v_t_315_, lean_object* v_ref_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_315_, v_ref_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_ref_elim(lean_object* v_motive_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_ref_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Doc_LinkTargetView_ctorElim___redArg(v_t_319_, v_ref_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(lean_object* v_kind_323_, lean_object* v_text_324_, lean_object* v_tok_325_){
_start:
{
lean_object* v_info_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_info_326_ = l_Lean_Syntax_getHeadInfo(v_tok_325_);
lean_inc(v_info_326_);
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v_info_326_);
lean_ctor_set(v___x_327_, 1, v_text_324_);
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_array_push(v___x_329_, v___x_327_);
v___x_331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_331_, 0, v_info_326_);
lean_ctor_set(v___x_331_, 1, v_kind_323_);
lean_ctor_set(v___x_331_, 2, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter___boxed(lean_object* v_kind_332_, lean_object* v_text_333_, lean_object* v_tok_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v_kind_332_, v_text_333_, v_tok_334_);
lean_dec(v_tok_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter_spec__0(lean_object* v_x_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_zero_338_; uint8_t v_isZero_339_; 
v_zero_338_ = lean_unsigned_to_nat(0u);
v_isZero_339_ = lean_nat_dec_eq(v_x_336_, v_zero_338_);
if (v_isZero_339_ == 1)
{
lean_dec(v_x_336_);
return v_x_337_;
}
else
{
uint32_t v___x_340_; lean_object* v_one_341_; lean_object* v_n_342_; lean_object* v___x_343_; 
v___x_340_ = 96;
v_one_341_ = lean_unsigned_to_nat(1u);
v_n_342_ = lean_nat_sub(v_x_336_, v_one_341_);
lean_dec(v_x_336_);
v___x_343_ = lean_string_push(v_x_337_, v___x_340_);
v_x_336_ = v_n_342_;
v_x_337_ = v___x_343_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(lean_object* v_value_352_, lean_object* v_tok_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_354_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1));
v___x_355_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___x_356_ = l_Lean_Doc_longestBacktickRun(v_value_352_);
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
v___x_359_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter_spec__0(v___x_358_, v___x_355_);
v___x_360_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_354_, v___x_359_, v_tok_353_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___boxed(lean_object* v_value_361_, lean_object* v_tok_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(v_value_361_, v_tok_362_);
lean_dec(v_tok_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence(lean_object* v_tok_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1));
v___x_373_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__2));
v___x_374_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_372_, v___x_373_, v_tok_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asFence___boxed(lean_object* v_tok_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_tok_375_);
lean_dec(v_tok_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(lean_object* v_tok_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1));
v___x_386_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__2));
v___x_387_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_385_, v___x_386_, v_tok_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___boxed(lean_object* v_tok_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(v_tok_388_);
lean_dec(v_tok_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(lean_object* v_tok_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Syntax_getHeadInfo(v_tok_390_);
switch(lean_obj_tag(v___x_391_))
{
case 0:
{
lean_object* v_leading_392_; lean_object* v_trailing_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_427_; 
v_leading_392_ = lean_ctor_get(v___x_391_, 0);
v_trailing_393_ = lean_ctor_get(v___x_391_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_428_ = lean_ctor_get(v___x_391_, 3);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_429_);
v___x_395_ = v___x_391_;
v_isShared_396_ = v_isSharedCheck_427_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_trailing_393_);
lean_inc(v_leading_392_);
lean_dec(v___x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_427_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v___x_397_; lean_object* v___x_398_; 
v___x_397_ = 0;
v___x_398_ = l_Lean_Syntax_getPos_x3f(v_tok_390_, v___x_397_);
if (lean_obj_tag(v___x_398_) == 1)
{
lean_object* v_val_399_; lean_object* v___x_400_; 
v_val_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = l_Lean_Syntax_getTailPos_x3f(v_tok_390_, v___x_397_);
if (lean_obj_tag(v___x_400_) == 1)
{
lean_object* v_val_401_; lean_object* v_str_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_422_; 
v_val_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v___x_400_, 1);
v_str_402_ = lean_ctor_get(v_leading_392_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_leading_392_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; lean_object* v_unused_424_; 
v_unused_423_ = lean_ctor_get(v_leading_392_, 2);
lean_dec(v_unused_423_);
v_unused_424_ = lean_ctor_get(v_leading_392_, 1);
lean_dec(v_unused_424_);
v___x_404_ = v_leading_392_;
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_str_402_);
lean_dec(v_leading_392_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_422_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
lean_inc_n(v_val_399_, 2);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 2, v_val_399_);
lean_ctor_set(v___x_404_, 1, v_val_399_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_str_402_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_val_399_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_val_399_);
v___x_407_ = v_reuseFailAlloc_421_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v_str_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_418_; 
v_str_408_ = lean_ctor_get(v_trailing_393_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_trailing_393_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; 
v_unused_419_ = lean_ctor_get(v_trailing_393_, 2);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_trailing_393_, 1);
lean_dec(v_unused_420_);
v___x_410_ = v_trailing_393_;
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_str_408_);
lean_dec(v_trailing_393_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_418_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
lean_inc_n(v_val_401_, 2);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 2, v_val_401_);
lean_ctor_set(v___x_410_, 1, v_val_401_);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_str_408_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_val_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_val_401_);
v___x_413_ = v_reuseFailAlloc_417_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_415_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 3, v_val_401_);
lean_ctor_set(v___x_395_, 2, v___x_413_);
lean_ctor_set(v___x_395_, 1, v_val_399_);
lean_ctor_set(v___x_395_, 0, v___x_407_);
v___x_415_ = v___x_395_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_val_399_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v___x_413_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_val_401_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
else
{
lean_object* v___x_425_; 
lean_dec(v___x_400_);
lean_dec(v_val_399_);
lean_del_object(v___x_395_);
lean_dec_ref(v_trailing_393_);
lean_dec_ref(v_leading_392_);
v___x_425_ = lean_box(2);
return v___x_425_;
}
}
else
{
lean_object* v___x_426_; 
lean_dec(v___x_398_);
lean_del_object(v___x_395_);
lean_dec_ref(v_trailing_393_);
lean_dec_ref(v_leading_392_);
v___x_426_ = lean_box(2);
return v___x_426_;
}
}
}
case 1:
{
uint8_t v_canonical_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_444_; 
v_canonical_430_ = lean_ctor_get_uint8(v___x_391_, sizeof(void*)*2);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_445_ = lean_ctor_get(v___x_391_, 1);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_446_);
v___x_432_ = v___x_391_;
v_isShared_433_ = v_isSharedCheck_444_;
goto v_resetjp_431_;
}
else
{
lean_dec(v___x_391_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_444_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; lean_object* v___x_435_; 
v___x_434_ = 0;
v___x_435_ = l_Lean_Syntax_getPos_x3f(v_tok_390_, v___x_434_);
if (lean_obj_tag(v___x_435_) == 1)
{
lean_object* v_val_436_; lean_object* v___x_437_; 
v_val_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc(v_val_436_);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = l_Lean_Syntax_getTailPos_x3f(v_tok_390_, v___x_434_);
if (lean_obj_tag(v___x_437_) == 1)
{
lean_object* v_val_438_; lean_object* v___x_440_; 
v_val_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v___x_437_, 1);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_val_438_);
lean_ctor_set(v___x_432_, 0, v_val_436_);
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_val_436_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_val_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_441_, sizeof(void*)*2, v_canonical_430_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_442_; 
lean_dec(v___x_437_);
lean_dec(v_val_436_);
lean_del_object(v___x_432_);
v___x_442_ = lean_box(2);
return v___x_442_;
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v___x_435_);
lean_del_object(v___x_432_);
v___x_443_ = lean_box(2);
return v___x_443_;
}
}
}
default: 
{
lean_object* v___x_447_; 
lean_dec(v___x_391_);
v___x_447_ = lean_box(2);
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo___boxed(lean_object* v_tok_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_tok_448_);
lean_dec(v_tok_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent(lean_object* v_value_450_, lean_object* v_tok_451_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_tok_451_);
v___x_453_ = l_Lean_Syntax_mkStrLit(v_value_450_, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_strLitOfContent___boxed(lean_object* v_value_454_, lean_object* v_tok_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Doc_strLitOfContent(v_value_454_, v_tok_455_);
lean_dec(v_tok_455_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(lean_object* v_tok_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Syntax_getHeadInfo(v_tok_457_);
switch(lean_obj_tag(v___x_458_))
{
case 0:
{
lean_object* v_leading_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_480_; 
v_leading_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; lean_object* v_unused_482_; lean_object* v_unused_483_; 
v_unused_481_ = lean_ctor_get(v___x_458_, 3);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v___x_458_, 2);
lean_dec(v_unused_482_);
v_unused_483_ = lean_ctor_get(v___x_458_, 1);
lean_dec(v_unused_483_);
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_480_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_leading_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_480_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; lean_object* v___x_464_; 
v___x_463_ = 0;
v___x_464_ = l_Lean_Syntax_getPos_x3f(v_tok_457_, v___x_463_);
if (lean_obj_tag(v___x_464_) == 1)
{
lean_object* v_val_465_; lean_object* v_str_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_476_; 
v_val_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_464_, 1);
v_str_466_ = lean_ctor_get(v_leading_459_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v_leading_459_);
if (v_isSharedCheck_476_ == 0)
{
lean_object* v_unused_477_; lean_object* v_unused_478_; 
v_unused_477_ = lean_ctor_get(v_leading_459_, 2);
lean_dec(v_unused_477_);
v_unused_478_ = lean_ctor_get(v_leading_459_, 1);
lean_dec(v_unused_478_);
v___x_468_ = v_leading_459_;
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_str_466_);
lean_dec(v_leading_459_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_476_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
lean_inc_n(v_val_465_, 2);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 2, v_val_465_);
lean_ctor_set(v___x_468_, 1, v_val_465_);
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_str_466_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_val_465_);
lean_ctor_set(v_reuseFailAlloc_475_, 2, v_val_465_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
lean_inc(v_val_465_);
lean_inc_ref(v___x_471_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 3, v_val_465_);
lean_ctor_set(v___x_461_, 2, v___x_471_);
lean_ctor_set(v___x_461_, 1, v_val_465_);
lean_ctor_set(v___x_461_, 0, v___x_471_);
v___x_473_ = v___x_461_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_val_465_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_val_465_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v___x_464_);
lean_del_object(v___x_461_);
lean_dec_ref(v_leading_459_);
v___x_479_ = lean_box(2);
return v___x_479_;
}
}
}
case 1:
{
uint8_t v_canonical_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_canonical_484_ = lean_ctor_get_uint8(v___x_458_, sizeof(void*)*2);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v___x_458_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v___x_458_, 0);
lean_dec(v_unused_497_);
v___x_486_ = v___x_458_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_dec(v___x_458_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; lean_object* v___x_489_; 
v___x_488_ = 0;
v___x_489_ = l_Lean_Syntax_getPos_x3f(v_tok_457_, v___x_488_);
if (lean_obj_tag(v___x_489_) == 1)
{
lean_object* v_val_490_; lean_object* v___x_492_; 
v_val_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc_n(v_val_490_, 2);
lean_dec_ref_known(v___x_489_, 1);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v_val_490_);
lean_ctor_set(v___x_486_, 0, v_val_490_);
v___x_492_ = v___x_486_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_val_490_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_val_490_);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, sizeof(void*)*2, v_canonical_484_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_494_; 
lean_dec(v___x_489_);
lean_del_object(v___x_486_);
v___x_494_ = lean_box(2);
return v___x_494_;
}
}
}
default: 
{
lean_object* v___x_498_; 
lean_dec(v___x_458_);
v___x_498_ = lean_box(2);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo___boxed(lean_object* v_tok_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v_tok_499_);
lean_dec(v_tok_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(lean_object* v___x_502_, lean_object* v_value_503_, lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
uint8_t v_decide_506_; 
v_decide_506_ = lean_nat_dec_eq(v_a_504_, v___x_502_);
if (v_decide_506_ == 0)
{
uint32_t v___x_507_; lean_object* v___x_508_; uint32_t v___x_509_; uint8_t v___x_510_; 
v___x_507_ = lean_string_utf8_get_fast(v_value_503_, v_a_504_);
v___x_508_ = lean_string_utf8_next_fast(v_value_503_, v_a_504_);
lean_dec(v_a_504_);
v___x_509_ = 92;
v___x_510_ = lean_uint32_dec_eq(v___x_507_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
v___x_511_ = lean_string_push(v_b_505_, v___x_507_);
v_a_504_ = v___x_508_;
v_b_505_ = v___x_511_;
goto _start;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___closed__0));
v___x_514_ = lean_string_append(v_b_505_, v___x_513_);
v_a_504_ = v___x_508_;
v_b_505_ = v___x_514_;
goto _start;
}
}
else
{
lean_dec(v_a_504_);
return v_b_505_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg___boxed(lean_object* v___x_516_, lean_object* v_value_517_, lean_object* v_a_518_, lean_object* v_b_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_516_, v_value_517_, v_a_518_, v_b_519_);
lean_dec_ref(v_value_517_);
lean_dec(v___x_516_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(lean_object* v_value_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_522_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_string_utf8_byte_size(v_value_521_);
lean_inc_ref(v_value_521_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v_value_521_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v___x_526_ = l_String_Slice_positions(v___x_525_);
lean_dec_ref_known(v___x_525_, 3);
v___x_527_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_524_, v_value_521_, v___x_526_, v___x_522_);
lean_dec_ref(v_value_521_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v_value_530_, lean_object* v_inst_531_, lean_object* v_R_532_, lean_object* v_a_533_, lean_object* v_b_534_, lean_object* v_c_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___redArg(v___x_529_, v_value_530_, v_a_533_, v_b_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0___boxed(lean_object* v___x_537_, lean_object* v___x_538_, lean_object* v_value_539_, lean_object* v_inst_540_, lean_object* v_R_541_, lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_c_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_View_0__Lean_Doc_escapeVersoText_spec__0(v___x_537_, v___x_538_, v_value_539_, v_inst_540_, v_R_541_, v_a_542_, v_b_543_, v_c_544_);
lean_dec_ref(v_value_539_);
lean_dec(v___x_538_);
lean_dec_ref(v___x_537_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom(lean_object* v_src_546_, lean_object* v_value_547_, uint8_t v_canonical_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_549_ = l_Lean_Doc_versoTextKind;
v___x_550_ = l___private_Lean_DocString_View_0__Lean_Doc_escapeVersoText(v_value_547_);
v___x_551_ = l_Lean_SourceInfo_fromRef(v_src_546_, v_canonical_548_);
v___x_552_ = l_Lean_Syntax_mkLit(v___x_549_, v___x_550_, v___x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFrom___boxed(lean_object* v_src_553_, lean_object* v_value_554_, lean_object* v_canonical_555_){
_start:
{
uint8_t v_canonical_boxed_556_; lean_object* v_res_557_; 
v_canonical_boxed_556_ = lean_unbox(v_canonical_555_);
v_res_557_ = l_Lean_Doc_mkVersoTextFrom(v_src_553_, v_value_554_, v_canonical_boxed_556_);
lean_dec(v_src_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom(lean_object* v_src_558_, lean_object* v_value_559_, uint8_t v_canonical_560_){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = l_Lean_Doc_versoRefKind;
v___x_562_ = l_Lean_SourceInfo_fromRef(v_src_558_, v_canonical_560_);
v___x_563_ = l_Lean_Syntax_mkLit(v___x_561_, v_value_559_, v___x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFrom___boxed(lean_object* v_src_564_, lean_object* v_value_565_, lean_object* v_canonical_566_){
_start:
{
uint8_t v_canonical_boxed_567_; lean_object* v_res_568_; 
v_canonical_boxed_567_ = lean_unbox(v_canonical_566_);
v_res_568_ = l_Lean_Doc_mkVersoRefNameFrom(v_src_564_, v_value_565_, v_canonical_boxed_567_);
lean_dec(v_src_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom(lean_object* v_src_569_, lean_object* v_value_570_, uint8_t v_canonical_571_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_572_ = l_Lean_Doc_versoLinkUrlKind;
v___x_573_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_570_);
v___x_574_ = l_Lean_SourceInfo_fromRef(v_src_569_, v_canonical_571_);
v___x_575_ = l_Lean_Syntax_mkLit(v___x_572_, v___x_573_, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFrom___boxed(lean_object* v_src_576_, lean_object* v_value_577_, lean_object* v_canonical_578_){
_start:
{
uint8_t v_canonical_boxed_579_; lean_object* v_res_580_; 
v_canonical_boxed_579_ = lean_unbox(v_canonical_578_);
v_res_580_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_src_576_, v_value_577_, v_canonical_boxed_579_);
lean_dec(v_src_576_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom(lean_object* v_src_581_, lean_object* v_value_582_, uint8_t v_canonical_583_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = l_Lean_Doc_versoImageAltKind;
v___x_585_ = l_Lean_Doc_escapeVersoImageAlt(v_value_582_);
v___x_586_ = l_Lean_SourceInfo_fromRef(v_src_581_, v_canonical_583_);
v___x_587_ = l_Lean_Syntax_mkLit(v___x_584_, v___x_585_, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFrom___boxed(lean_object* v_src_588_, lean_object* v_value_589_, lean_object* v_canonical_590_){
_start:
{
uint8_t v_canonical_boxed_591_; lean_object* v_res_592_; 
v_canonical_boxed_591_ = lean_unbox(v_canonical_590_);
v_res_592_ = l_Lean_Doc_mkVersoImageAltFrom(v_src_588_, v_value_589_, v_canonical_boxed_591_);
lean_dec(v_src_588_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom(lean_object* v_src_593_, lean_object* v_value_594_, uint8_t v_canonical_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = l_Lean_Doc_versoLinkRefUrlKind;
v___x_597_ = l_Lean_SourceInfo_fromRef(v_src_593_, v_canonical_595_);
v___x_598_ = l_Lean_Syntax_mkLit(v___x_596_, v_value_594_, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFrom___boxed(lean_object* v_src_599_, lean_object* v_value_600_, lean_object* v_canonical_601_){
_start:
{
uint8_t v_canonical_boxed_602_; lean_object* v_res_603_; 
v_canonical_boxed_602_ = lean_unbox(v_canonical_601_);
v_res_603_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_src_599_, v_value_600_, v_canonical_boxed_602_);
lean_dec(v_src_599_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom(lean_object* v_src_605_, lean_object* v_value_606_, uint8_t v_canonical_607_){
_start:
{
lean_object* v___y_609_; uint8_t v___x_613_; 
lean_inc_ref(v_value_606_);
v___x_613_ = l_Lean_Doc_versoCodeBoundarySpaces(v_value_606_);
if (v___x_613_ == 0)
{
v___y_609_ = v_value_606_;
goto v___jp_608_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeFrom___closed__0));
v___x_615_ = lean_string_append(v___x_614_, v_value_606_);
lean_dec_ref(v_value_606_);
v___x_616_ = lean_string_append(v___x_615_, v___x_614_);
v___y_609_ = v___x_616_;
goto v___jp_608_;
}
v___jp_608_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = l_Lean_Doc_versoCodeKind;
v___x_611_ = l_Lean_SourceInfo_fromRef(v_src_605_, v_canonical_607_);
v___x_612_ = l_Lean_Syntax_mkLit(v___x_610_, v___y_609_, v___x_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFrom___boxed(lean_object* v_src_617_, lean_object* v_value_618_, lean_object* v_canonical_619_){
_start:
{
uint8_t v_canonical_boxed_620_; lean_object* v_res_621_; 
v_canonical_boxed_620_ = lean_unbox(v_canonical_619_);
v_res_621_ = l_Lean_Doc_mkVersoCodeFrom(v_src_617_, v_value_618_, v_canonical_boxed_620_);
lean_dec(v_src_617_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom(lean_object* v_src_625_, lean_object* v_value_626_, uint8_t v_canonical_627_){
_start:
{
lean_object* v_info_628_; lean_object* v___x_629_; lean_object* v_line_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_info_628_ = l_Lean_SourceInfo_fromRef(v_src_625_, v_canonical_627_);
v___x_629_ = l_Lean_Doc_versoCodeBlockLineKind;
lean_inc(v_info_628_);
v_line_630_ = l_Lean_Syntax_mkLit(v___x_629_, v_value_626_, v_info_628_);
v___x_631_ = l_Lean_Doc_versoCodeBlockKind;
v___x_632_ = lean_unsigned_to_nat(1u);
v___x_633_ = lean_mk_empty_array_with_capacity(v___x_632_);
lean_inc_ref(v___x_633_);
v___x_634_ = lean_array_push(v___x_633_, v_line_630_);
v___x_635_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_636_ = lean_box(2);
v___x_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_634_);
v___x_638_ = lean_array_push(v___x_633_, v___x_637_);
v___x_639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_639_, 0, v_info_628_);
lean_ctor_set(v___x_639_, 1, v___x_631_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFrom___boxed(lean_object* v_src_640_, lean_object* v_value_641_, lean_object* v_canonical_642_){
_start:
{
uint8_t v_canonical_boxed_643_; lean_object* v_res_644_; 
v_canonical_boxed_643_ = lean_unbox(v_canonical_642_);
v_res_644_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_src_640_, v_value_641_, v_canonical_boxed_643_);
lean_dec(v_src_640_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom(lean_object* v_src_654_, uint8_t v_canonical_655_){
_start:
{
lean_object* v_info_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_info_656_ = l_Lean_SourceInfo_fromRef(v_src_654_, v_canonical_655_);
v___x_657_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_658_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__3));
lean_inc(v_info_656_);
v___x_659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_659_, 0, v_info_656_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_unsigned_to_nat(1u);
v___x_661_ = lean_mk_empty_array_with_capacity(v___x_660_);
v___x_662_ = lean_array_push(v___x_661_, v___x_659_);
v___x_663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_663_, 0, v_info_656_);
lean_ctor_set(v___x_663_, 1, v___x_657_);
lean_ctor_set(v___x_663_, 2, v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFrom___boxed(lean_object* v_src_664_, lean_object* v_canonical_665_){
_start:
{
uint8_t v_canonical_boxed_666_; lean_object* v_res_667_; 
v_canonical_boxed_666_ = lean_unbox(v_canonical_665_);
v_res_667_ = l_Lean_Doc_mkVersoLinebreakFrom(v_src_664_, v_canonical_boxed_666_);
lean_dec(v_src_664_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(uint8_t v_canonical_668_, lean_object* v_toPure_669_, lean_object* v_____do__lift_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = l_Lean_Doc_mkVersoLinebreakFrom(v_____do__lift_670_, v_canonical_668_);
v___x_672_ = lean_apply_2(v_toPure_669_, lean_box(0), v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed(lean_object* v_canonical_673_, lean_object* v_toPure_674_, lean_object* v_____do__lift_675_){
_start:
{
uint8_t v_canonical_boxed_676_; lean_object* v_res_677_; 
v_canonical_boxed_676_ = lean_unbox(v_canonical_673_);
v_res_677_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0(v_canonical_boxed_676_, v_toPure_674_, v_____do__lift_675_);
lean_dec(v_____do__lift_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg(lean_object* v_inst_678_, lean_object* v_inst_679_, uint8_t v_canonical_680_){
_start:
{
lean_object* v_toApplicative_681_; lean_object* v_toBind_682_; lean_object* v_getRef_683_; lean_object* v_toPure_684_; lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___x_687_; 
v_toApplicative_681_ = lean_ctor_get(v_inst_678_, 0);
lean_inc_ref(v_toApplicative_681_);
v_toBind_682_ = lean_ctor_get(v_inst_678_, 1);
lean_inc(v_toBind_682_);
lean_dec_ref(v_inst_678_);
v_getRef_683_ = lean_ctor_get(v_inst_679_, 0);
lean_inc(v_getRef_683_);
lean_dec_ref(v_inst_679_);
v_toPure_684_ = lean_ctor_get(v_toApplicative_681_, 1);
lean_inc(v_toPure_684_);
lean_dec_ref(v_toApplicative_681_);
v___x_685_ = lean_box(v_canonical_680_);
v___f_686_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinebreakFromRef___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_686_, 0, v___x_685_);
lean_closure_set(v___f_686_, 1, v_toPure_684_);
v___x_687_ = lean_apply_4(v_toBind_682_, lean_box(0), lean_box(0), v_getRef_683_, v___f_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___redArg___boxed(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_canonical_690_){
_start:
{
uint8_t v_canonical_boxed_691_; lean_object* v_res_692_; 
v_canonical_boxed_691_ = lean_unbox(v_canonical_690_);
v_res_692_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_688_, v_inst_689_, v_canonical_boxed_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef(lean_object* v_m_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, uint8_t v_canonical_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Doc_mkVersoLinebreakFromRef___redArg(v_inst_694_, v_inst_695_, v_canonical_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinebreakFromRef___boxed(lean_object* v_m_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_canonical_701_){
_start:
{
uint8_t v_canonical_boxed_702_; lean_object* v_res_703_; 
v_canonical_boxed_702_ = lean_unbox(v_canonical_701_);
v_res_703_ = l_Lean_Doc_mkVersoLinebreakFromRef(v_m_698_, v_inst_699_, v_inst_700_, v_canonical_boxed_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(lean_object* v_value_704_, uint8_t v_canonical_705_, lean_object* v_toPure_706_, lean_object* v_____do__lift_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_Lean_Doc_mkVersoTextFrom(v_____do__lift_707_, v_value_704_, v_canonical_705_);
v___x_709_ = lean_apply_2(v_toPure_706_, lean_box(0), v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed(lean_object* v_value_710_, lean_object* v_canonical_711_, lean_object* v_toPure_712_, lean_object* v_____do__lift_713_){
_start:
{
uint8_t v_canonical_boxed_714_; lean_object* v_res_715_; 
v_canonical_boxed_714_ = lean_unbox(v_canonical_711_);
v_res_715_ = l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0(v_value_710_, v_canonical_boxed_714_, v_toPure_712_, v_____do__lift_713_);
lean_dec(v_____do__lift_713_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg(lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_value_718_, uint8_t v_canonical_719_){
_start:
{
lean_object* v_toApplicative_720_; lean_object* v_toBind_721_; lean_object* v_getRef_722_; lean_object* v_toPure_723_; lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v___x_726_; 
v_toApplicative_720_ = lean_ctor_get(v_inst_716_, 0);
lean_inc_ref(v_toApplicative_720_);
v_toBind_721_ = lean_ctor_get(v_inst_716_, 1);
lean_inc(v_toBind_721_);
lean_dec_ref(v_inst_716_);
v_getRef_722_ = lean_ctor_get(v_inst_717_, 0);
lean_inc(v_getRef_722_);
lean_dec_ref(v_inst_717_);
v_toPure_723_ = lean_ctor_get(v_toApplicative_720_, 1);
lean_inc(v_toPure_723_);
lean_dec_ref(v_toApplicative_720_);
v___x_724_ = lean_box(v_canonical_719_);
v___f_725_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoTextFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_725_, 0, v_value_718_);
lean_closure_set(v___f_725_, 1, v___x_724_);
lean_closure_set(v___f_725_, 2, v_toPure_723_);
v___x_726_ = lean_apply_4(v_toBind_721_, lean_box(0), lean_box(0), v_getRef_722_, v___f_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___redArg___boxed(lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_value_729_, lean_object* v_canonical_730_){
_start:
{
uint8_t v_canonical_boxed_731_; lean_object* v_res_732_; 
v_canonical_boxed_731_ = lean_unbox(v_canonical_730_);
v_res_732_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_727_, v_inst_728_, v_value_729_, v_canonical_boxed_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef(lean_object* v_m_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_value_736_, uint8_t v_canonical_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Doc_mkVersoTextFromRef___redArg(v_inst_734_, v_inst_735_, v_value_736_, v_canonical_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoTextFromRef___boxed(lean_object* v_m_739_, lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_value_742_, lean_object* v_canonical_743_){
_start:
{
uint8_t v_canonical_boxed_744_; lean_object* v_res_745_; 
v_canonical_boxed_744_ = lean_unbox(v_canonical_743_);
v_res_745_ = l_Lean_Doc_mkVersoTextFromRef(v_m_739_, v_inst_740_, v_inst_741_, v_value_742_, v_canonical_boxed_744_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(lean_object* v_value_746_, uint8_t v_canonical_747_, lean_object* v_toPure_748_, lean_object* v_____do__lift_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = l_Lean_Doc_mkVersoRefNameFrom(v_____do__lift_749_, v_value_746_, v_canonical_747_);
v___x_751_ = lean_apply_2(v_toPure_748_, lean_box(0), v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed(lean_object* v_value_752_, lean_object* v_canonical_753_, lean_object* v_toPure_754_, lean_object* v_____do__lift_755_){
_start:
{
uint8_t v_canonical_boxed_756_; lean_object* v_res_757_; 
v_canonical_boxed_756_ = lean_unbox(v_canonical_753_);
v_res_757_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0(v_value_752_, v_canonical_boxed_756_, v_toPure_754_, v_____do__lift_755_);
lean_dec(v_____do__lift_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg(lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_value_760_, uint8_t v_canonical_761_){
_start:
{
lean_object* v_toApplicative_762_; lean_object* v_toBind_763_; lean_object* v_getRef_764_; lean_object* v_toPure_765_; lean_object* v___x_766_; lean_object* v___f_767_; lean_object* v___x_768_; 
v_toApplicative_762_ = lean_ctor_get(v_inst_758_, 0);
lean_inc_ref(v_toApplicative_762_);
v_toBind_763_ = lean_ctor_get(v_inst_758_, 1);
lean_inc(v_toBind_763_);
lean_dec_ref(v_inst_758_);
v_getRef_764_ = lean_ctor_get(v_inst_759_, 0);
lean_inc(v_getRef_764_);
lean_dec_ref(v_inst_759_);
v_toPure_765_ = lean_ctor_get(v_toApplicative_762_, 1);
lean_inc(v_toPure_765_);
lean_dec_ref(v_toApplicative_762_);
v___x_766_ = lean_box(v_canonical_761_);
v___f_767_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoRefNameFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_767_, 0, v_value_760_);
lean_closure_set(v___f_767_, 1, v___x_766_);
lean_closure_set(v___f_767_, 2, v_toPure_765_);
v___x_768_ = lean_apply_4(v_toBind_763_, lean_box(0), lean_box(0), v_getRef_764_, v___f_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___redArg___boxed(lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_value_771_, lean_object* v_canonical_772_){
_start:
{
uint8_t v_canonical_boxed_773_; lean_object* v_res_774_; 
v_canonical_boxed_773_ = lean_unbox(v_canonical_772_);
v_res_774_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_769_, v_inst_770_, v_value_771_, v_canonical_boxed_773_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef(lean_object* v_m_775_, lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_value_778_, uint8_t v_canonical_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Doc_mkVersoRefNameFromRef___redArg(v_inst_776_, v_inst_777_, v_value_778_, v_canonical_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoRefNameFromRef___boxed(lean_object* v_m_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_value_784_, lean_object* v_canonical_785_){
_start:
{
uint8_t v_canonical_boxed_786_; lean_object* v_res_787_; 
v_canonical_boxed_786_ = lean_unbox(v_canonical_785_);
v_res_787_ = l_Lean_Doc_mkVersoRefNameFromRef(v_m_781_, v_inst_782_, v_inst_783_, v_value_784_, v_canonical_boxed_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(lean_object* v_value_788_, uint8_t v_canonical_789_, lean_object* v_toPure_790_, lean_object* v_____do__lift_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_____do__lift_791_, v_value_788_, v_canonical_789_);
v___x_793_ = lean_apply_2(v_toPure_790_, lean_box(0), v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_794_, lean_object* v_canonical_795_, lean_object* v_toPure_796_, lean_object* v_____do__lift_797_){
_start:
{
uint8_t v_canonical_boxed_798_; lean_object* v_res_799_; 
v_canonical_boxed_798_ = lean_unbox(v_canonical_795_);
v_res_799_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0(v_value_794_, v_canonical_boxed_798_, v_toPure_796_, v_____do__lift_797_);
lean_dec(v_____do__lift_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_value_802_, uint8_t v_canonical_803_){
_start:
{
lean_object* v_toApplicative_804_; lean_object* v_toBind_805_; lean_object* v_getRef_806_; lean_object* v_toPure_807_; lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; 
v_toApplicative_804_ = lean_ctor_get(v_inst_800_, 0);
lean_inc_ref(v_toApplicative_804_);
v_toBind_805_ = lean_ctor_get(v_inst_800_, 1);
lean_inc(v_toBind_805_);
lean_dec_ref(v_inst_800_);
v_getRef_806_ = lean_ctor_get(v_inst_801_, 0);
lean_inc(v_getRef_806_);
lean_dec_ref(v_inst_801_);
v_toPure_807_ = lean_ctor_get(v_toApplicative_804_, 1);
lean_inc(v_toPure_807_);
lean_dec_ref(v_toApplicative_804_);
v___x_808_ = lean_box(v_canonical_803_);
v___f_809_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_809_, 0, v_value_802_);
lean_closure_set(v___f_809_, 1, v___x_808_);
lean_closure_set(v___f_809_, 2, v_toPure_807_);
v___x_810_ = lean_apply_4(v_toBind_805_, lean_box(0), lean_box(0), v_getRef_806_, v___f_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___redArg___boxed(lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_value_813_, lean_object* v_canonical_814_){
_start:
{
uint8_t v_canonical_boxed_815_; lean_object* v_res_816_; 
v_canonical_boxed_815_ = lean_unbox(v_canonical_814_);
v_res_816_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_811_, v_inst_812_, v_value_813_, v_canonical_boxed_815_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef(lean_object* v_m_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_value_820_, uint8_t v_canonical_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Doc_mkVersoLinkUrlFromRef___redArg(v_inst_818_, v_inst_819_, v_value_820_, v_canonical_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkUrlFromRef___boxed(lean_object* v_m_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_value_826_, lean_object* v_canonical_827_){
_start:
{
uint8_t v_canonical_boxed_828_; lean_object* v_res_829_; 
v_canonical_boxed_828_ = lean_unbox(v_canonical_827_);
v_res_829_ = l_Lean_Doc_mkVersoLinkUrlFromRef(v_m_823_, v_inst_824_, v_inst_825_, v_value_826_, v_canonical_boxed_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(lean_object* v_value_830_, uint8_t v_canonical_831_, lean_object* v_toPure_832_, lean_object* v_____do__lift_833_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = l_Lean_Doc_mkVersoImageAltFrom(v_____do__lift_833_, v_value_830_, v_canonical_831_);
v___x_835_ = lean_apply_2(v_toPure_832_, lean_box(0), v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed(lean_object* v_value_836_, lean_object* v_canonical_837_, lean_object* v_toPure_838_, lean_object* v_____do__lift_839_){
_start:
{
uint8_t v_canonical_boxed_840_; lean_object* v_res_841_; 
v_canonical_boxed_840_ = lean_unbox(v_canonical_837_);
v_res_841_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0(v_value_836_, v_canonical_boxed_840_, v_toPure_838_, v_____do__lift_839_);
lean_dec(v_____do__lift_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg(lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_value_844_, uint8_t v_canonical_845_){
_start:
{
lean_object* v_toApplicative_846_; lean_object* v_toBind_847_; lean_object* v_getRef_848_; lean_object* v_toPure_849_; lean_object* v___x_850_; lean_object* v___f_851_; lean_object* v___x_852_; 
v_toApplicative_846_ = lean_ctor_get(v_inst_842_, 0);
lean_inc_ref(v_toApplicative_846_);
v_toBind_847_ = lean_ctor_get(v_inst_842_, 1);
lean_inc(v_toBind_847_);
lean_dec_ref(v_inst_842_);
v_getRef_848_ = lean_ctor_get(v_inst_843_, 0);
lean_inc(v_getRef_848_);
lean_dec_ref(v_inst_843_);
v_toPure_849_ = lean_ctor_get(v_toApplicative_846_, 1);
lean_inc(v_toPure_849_);
lean_dec_ref(v_toApplicative_846_);
v___x_850_ = lean_box(v_canonical_845_);
v___f_851_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoImageAltFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_851_, 0, v_value_844_);
lean_closure_set(v___f_851_, 1, v___x_850_);
lean_closure_set(v___f_851_, 2, v_toPure_849_);
v___x_852_ = lean_apply_4(v_toBind_847_, lean_box(0), lean_box(0), v_getRef_848_, v___f_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___redArg___boxed(lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_value_855_, lean_object* v_canonical_856_){
_start:
{
uint8_t v_canonical_boxed_857_; lean_object* v_res_858_; 
v_canonical_boxed_857_ = lean_unbox(v_canonical_856_);
v_res_858_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_853_, v_inst_854_, v_value_855_, v_canonical_boxed_857_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef(lean_object* v_m_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_value_862_, uint8_t v_canonical_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Doc_mkVersoImageAltFromRef___redArg(v_inst_860_, v_inst_861_, v_value_862_, v_canonical_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoImageAltFromRef___boxed(lean_object* v_m_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_value_868_, lean_object* v_canonical_869_){
_start:
{
uint8_t v_canonical_boxed_870_; lean_object* v_res_871_; 
v_canonical_boxed_870_ = lean_unbox(v_canonical_869_);
v_res_871_ = l_Lean_Doc_mkVersoImageAltFromRef(v_m_865_, v_inst_866_, v_inst_867_, v_value_868_, v_canonical_boxed_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(lean_object* v_value_872_, uint8_t v_canonical_873_, lean_object* v_toPure_874_, lean_object* v_____do__lift_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_____do__lift_875_, v_value_872_, v_canonical_873_);
v___x_877_ = lean_apply_2(v_toPure_874_, lean_box(0), v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed(lean_object* v_value_878_, lean_object* v_canonical_879_, lean_object* v_toPure_880_, lean_object* v_____do__lift_881_){
_start:
{
uint8_t v_canonical_boxed_882_; lean_object* v_res_883_; 
v_canonical_boxed_882_ = lean_unbox(v_canonical_879_);
v_res_883_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0(v_value_878_, v_canonical_boxed_882_, v_toPure_880_, v_____do__lift_881_);
lean_dec(v_____do__lift_881_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_value_886_, uint8_t v_canonical_887_){
_start:
{
lean_object* v_toApplicative_888_; lean_object* v_toBind_889_; lean_object* v_getRef_890_; lean_object* v_toPure_891_; lean_object* v___x_892_; lean_object* v___f_893_; lean_object* v___x_894_; 
v_toApplicative_888_ = lean_ctor_get(v_inst_884_, 0);
lean_inc_ref(v_toApplicative_888_);
v_toBind_889_ = lean_ctor_get(v_inst_884_, 1);
lean_inc(v_toBind_889_);
lean_dec_ref(v_inst_884_);
v_getRef_890_ = lean_ctor_get(v_inst_885_, 0);
lean_inc(v_getRef_890_);
lean_dec_ref(v_inst_885_);
v_toPure_891_ = lean_ctor_get(v_toApplicative_888_, 1);
lean_inc(v_toPure_891_);
lean_dec_ref(v_toApplicative_888_);
v___x_892_ = lean_box(v_canonical_887_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_893_, 0, v_value_886_);
lean_closure_set(v___f_893_, 1, v___x_892_);
lean_closure_set(v___f_893_, 2, v_toPure_891_);
v___x_894_ = lean_apply_4(v_toBind_889_, lean_box(0), lean_box(0), v_getRef_890_, v___f_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg___boxed(lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_value_897_, lean_object* v_canonical_898_){
_start:
{
uint8_t v_canonical_boxed_899_; lean_object* v_res_900_; 
v_canonical_boxed_899_ = lean_unbox(v_canonical_898_);
v_res_900_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_895_, v_inst_896_, v_value_897_, v_canonical_boxed_899_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef(lean_object* v_m_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_value_904_, uint8_t v_canonical_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef___redArg(v_inst_902_, v_inst_903_, v_value_904_, v_canonical_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoLinkRefUrlFromRef___boxed(lean_object* v_m_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_value_910_, lean_object* v_canonical_911_){
_start:
{
uint8_t v_canonical_boxed_912_; lean_object* v_res_913_; 
v_canonical_boxed_912_ = lean_unbox(v_canonical_911_);
v_res_913_ = l_Lean_Doc_mkVersoLinkRefUrlFromRef(v_m_907_, v_inst_908_, v_inst_909_, v_value_910_, v_canonical_boxed_912_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(lean_object* v_value_914_, uint8_t v_canonical_915_, lean_object* v_toPure_916_, lean_object* v_____do__lift_917_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = l_Lean_Doc_mkVersoCodeFrom(v_____do__lift_917_, v_value_914_, v_canonical_915_);
v___x_919_ = lean_apply_2(v_toPure_916_, lean_box(0), v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed(lean_object* v_value_920_, lean_object* v_canonical_921_, lean_object* v_toPure_922_, lean_object* v_____do__lift_923_){
_start:
{
uint8_t v_canonical_boxed_924_; lean_object* v_res_925_; 
v_canonical_boxed_924_ = lean_unbox(v_canonical_921_);
v_res_925_ = l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0(v_value_920_, v_canonical_boxed_924_, v_toPure_922_, v_____do__lift_923_);
lean_dec(v_____do__lift_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg(lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_value_928_, uint8_t v_canonical_929_){
_start:
{
lean_object* v_toApplicative_930_; lean_object* v_toBind_931_; lean_object* v_getRef_932_; lean_object* v_toPure_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___x_936_; 
v_toApplicative_930_ = lean_ctor_get(v_inst_926_, 0);
lean_inc_ref(v_toApplicative_930_);
v_toBind_931_ = lean_ctor_get(v_inst_926_, 1);
lean_inc(v_toBind_931_);
lean_dec_ref(v_inst_926_);
v_getRef_932_ = lean_ctor_get(v_inst_927_, 0);
lean_inc(v_getRef_932_);
lean_dec_ref(v_inst_927_);
v_toPure_933_ = lean_ctor_get(v_toApplicative_930_, 1);
lean_inc(v_toPure_933_);
lean_dec_ref(v_toApplicative_930_);
v___x_934_ = lean_box(v_canonical_929_);
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_935_, 0, v_value_928_);
lean_closure_set(v___f_935_, 1, v___x_934_);
lean_closure_set(v___f_935_, 2, v_toPure_933_);
v___x_936_ = lean_apply_4(v_toBind_931_, lean_box(0), lean_box(0), v_getRef_932_, v___f_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___redArg___boxed(lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_value_939_, lean_object* v_canonical_940_){
_start:
{
uint8_t v_canonical_boxed_941_; lean_object* v_res_942_; 
v_canonical_boxed_941_ = lean_unbox(v_canonical_940_);
v_res_942_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_937_, v_inst_938_, v_value_939_, v_canonical_boxed_941_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef(lean_object* v_m_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_value_946_, uint8_t v_canonical_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Doc_mkVersoCodeFromRef___redArg(v_inst_944_, v_inst_945_, v_value_946_, v_canonical_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeFromRef___boxed(lean_object* v_m_949_, lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_value_952_, lean_object* v_canonical_953_){
_start:
{
uint8_t v_canonical_boxed_954_; lean_object* v_res_955_; 
v_canonical_boxed_954_ = lean_unbox(v_canonical_953_);
v_res_955_ = l_Lean_Doc_mkVersoCodeFromRef(v_m_949_, v_inst_950_, v_inst_951_, v_value_952_, v_canonical_boxed_954_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(lean_object* v_value_956_, uint8_t v_canonical_957_, lean_object* v_toPure_958_, lean_object* v_____do__lift_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_____do__lift_959_, v_value_956_, v_canonical_957_);
v___x_961_ = lean_apply_2(v_toPure_958_, lean_box(0), v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed(lean_object* v_value_962_, lean_object* v_canonical_963_, lean_object* v_toPure_964_, lean_object* v_____do__lift_965_){
_start:
{
uint8_t v_canonical_boxed_966_; lean_object* v_res_967_; 
v_canonical_boxed_966_ = lean_unbox(v_canonical_963_);
v_res_967_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0(v_value_962_, v_canonical_boxed_966_, v_toPure_964_, v_____do__lift_965_);
lean_dec(v_____do__lift_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_value_970_, uint8_t v_canonical_971_){
_start:
{
lean_object* v_toApplicative_972_; lean_object* v_toBind_973_; lean_object* v_getRef_974_; lean_object* v_toPure_975_; lean_object* v___x_976_; lean_object* v___f_977_; lean_object* v___x_978_; 
v_toApplicative_972_ = lean_ctor_get(v_inst_968_, 0);
lean_inc_ref(v_toApplicative_972_);
v_toBind_973_ = lean_ctor_get(v_inst_968_, 1);
lean_inc(v_toBind_973_);
lean_dec_ref(v_inst_968_);
v_getRef_974_ = lean_ctor_get(v_inst_969_, 0);
lean_inc(v_getRef_974_);
lean_dec_ref(v_inst_969_);
v_toPure_975_ = lean_ctor_get(v_toApplicative_972_, 1);
lean_inc(v_toPure_975_);
lean_dec_ref(v_toApplicative_972_);
v___x_976_ = lean_box(v_canonical_971_);
v___f_977_ = lean_alloc_closure((void*)(l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_977_, 0, v_value_970_);
lean_closure_set(v___f_977_, 1, v___x_976_);
lean_closure_set(v___f_977_, 2, v_toPure_975_);
v___x_978_ = lean_apply_4(v_toBind_973_, lean_box(0), lean_box(0), v_getRef_974_, v___f_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___redArg___boxed(lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_value_981_, lean_object* v_canonical_982_){
_start:
{
uint8_t v_canonical_boxed_983_; lean_object* v_res_984_; 
v_canonical_boxed_983_ = lean_unbox(v_canonical_982_);
v_res_984_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_979_, v_inst_980_, v_value_981_, v_canonical_boxed_983_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef(lean_object* v_m_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_value_988_, uint8_t v_canonical_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Doc_mkVersoCodeBlockFromRef___redArg(v_inst_986_, v_inst_987_, v_value_988_, v_canonical_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_mkVersoCodeBlockFromRef___boxed(lean_object* v_m_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_value_994_, lean_object* v_canonical_995_){
_start:
{
uint8_t v_canonical_boxed_996_; lean_object* v_res_997_; 
v_canonical_boxed_996_ = lean_unbox(v_canonical_995_);
v_res_997_ = l_Lean_Doc_mkVersoCodeBlockFromRef(v_m_991_, v_inst_992_, v_inst_993_, v_value_994_, v_canonical_boxed_996_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom(lean_object* v_text_998_, lean_object* v_tok_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = l_Lean_Syntax_getHeadInfo(v_tok_999_);
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_text_998_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asAtom___boxed(lean_object* v_text_1002_, lean_object* v_tok_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v_text_1002_, v_tok_1003_);
lean_dec(v_tok_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_asNode(lean_object* v_kind_1005_, lean_object* v_args_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_box(2);
v___x_1008_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_kind_1005_);
lean_ctor_set(v___x_1008_, 2, v_args_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_argValToParser(lean_object* v_stx_1028_){
_start:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_Doc_argValToParser___closed__2));
lean_inc(v_stx_1028_);
v___x_1030_ = l_Lean_Syntax_isOfKind(v_stx_1028_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; uint8_t v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_Doc_argValToParser___closed__4));
lean_inc(v_stx_1028_);
v___x_1032_ = l_Lean_Syntax_isOfKind(v_stx_1028_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_Doc_argValToParser___closed__6));
lean_inc(v_stx_1028_);
v___x_1034_ = l_Lean_Syntax_isOfKind(v_stx_1028_, v___x_1033_);
if (v___x_1034_ == 0)
{
return v_stx_1028_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = l_Lean_Syntax_getArg(v_stx_1028_, v___x_1035_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v___x_1036_);
v___x_1044_ = l_Lean_Syntax_isOfKind(v___x_1036_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_dec(v___x_1036_);
return v_stx_1028_;
}
else
{
lean_dec(v_stx_1028_);
goto v___jp_1037_;
}
}
else
{
lean_dec(v_stx_1028_);
goto v___jp_1037_;
}
v___jp_1037_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1038_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__9));
v___x_1039_ = lean_unsigned_to_nat(1u);
v___x_1040_ = lean_mk_empty_array_with_capacity(v___x_1039_);
v___x_1041_ = lean_array_push(v___x_1040_, v___x_1036_);
v___x_1042_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1038_, v___x_1041_);
return v___x_1042_;
}
}
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = l_Lean_Syntax_getArg(v_stx_1028_, v___x_1045_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__11));
lean_inc(v___x_1046_);
v___x_1054_ = l_Lean_Syntax_isOfKind(v___x_1046_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v___x_1046_);
return v_stx_1028_;
}
else
{
lean_dec(v_stx_1028_);
goto v___jp_1047_;
}
}
else
{
lean_dec(v_stx_1028_);
goto v___jp_1047_;
}
v___jp_1047_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1048_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__7));
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1051_ = lean_array_push(v___x_1050_, v___x_1046_);
v___x_1052_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1048_, v___x_1051_);
return v___x_1052_;
}
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = l_Lean_Syntax_getArg(v_stx_1028_, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1056_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v___x_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec(v___x_1056_);
return v_stx_1028_;
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec(v_stx_1028_);
v___x_1059_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__5));
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1061_ = lean_mk_empty_array_with_capacity(v___x_1060_);
v___x_1062_ = lean_array_push(v___x_1061_, v___x_1056_);
v___x_1063_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1059_, v___x_1062_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_docArgToParser(lean_object* v_stx_1089_){
_start:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__0));
lean_inc(v_stx_1089_);
v___x_1091_ = l_Lean_Syntax_isOfKind(v_stx_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__1));
lean_inc(v_stx_1089_);
v___x_1093_ = l_Lean_Syntax_isOfKind(v_stx_1089_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__2));
lean_inc(v_stx_1089_);
v___x_1095_ = l_Lean_Syntax_isOfKind(v_stx_1089_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__3));
lean_inc(v_stx_1089_);
v___x_1097_ = l_Lean_Syntax_isOfKind(v_stx_1089_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_Doc_docArgToParser___closed__4));
lean_inc(v_stx_1089_);
v___x_1099_ = l_Lean_Syntax_isOfKind(v_stx_1089_, v___x_1098_);
if (v___x_1099_ == 0)
{
return v_stx_1089_;
}
else
{
lean_object* v___x_1100_; lean_object* v_tk_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v_tk_1101_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1100_);
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1102_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1103_);
v___x_1112_ = l_Lean_Syntax_isOfKind(v___x_1103_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_dec(v___x_1103_);
lean_dec(v_tk_1101_);
return v_stx_1089_;
}
else
{
lean_dec(v_stx_1089_);
goto v___jp_1104_;
}
}
else
{
lean_dec(v_stx_1089_);
goto v___jp_1104_;
}
v___jp_1104_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1105_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__10));
v___x_1106_ = lean_unsigned_to_nat(2u);
v___x_1107_ = lean_mk_empty_array_with_capacity(v___x_1106_);
v___x_1108_ = lean_array_push(v___x_1107_, v_tk_1101_);
v___x_1109_ = lean_array_push(v___x_1108_, v___x_1103_);
v___x_1110_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1105_, v___x_1109_);
return v___x_1110_;
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v_tk_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v_tk_1114_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1113_);
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1115_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1116_);
v___x_1125_ = l_Lean_Syntax_isOfKind(v___x_1116_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_dec(v___x_1116_);
lean_dec(v_tk_1114_);
return v_stx_1089_;
}
else
{
lean_dec(v_stx_1089_);
goto v___jp_1117_;
}
}
else
{
lean_dec(v_stx_1089_);
goto v___jp_1117_;
}
v___jp_1117_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1118_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__8));
v___x_1119_ = lean_unsigned_to_nat(2u);
v___x_1120_ = lean_mk_empty_array_with_capacity(v___x_1119_);
v___x_1121_ = lean_array_push(v___x_1120_, v_tk_1114_);
v___x_1122_ = lean_array_push(v___x_1121_, v___x_1116_);
v___x_1123_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1118_, v___x_1122_);
return v___x_1123_;
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1126_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1127_);
v___x_1142_ = l_Lean_Syntax_isOfKind(v___x_1127_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec(v___x_1127_);
return v_stx_1089_;
}
else
{
goto v___jp_1128_;
}
}
else
{
goto v___jp_1128_;
}
v___jp_1128_:
{
lean_object* v___x_1129_; lean_object* v_eq_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1129_ = lean_unsigned_to_nat(1u);
v_eq_1130_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(2u);
v___x_1132_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1131_);
lean_dec(v_stx_1089_);
v___x_1133_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__6));
v___x_1134_ = l_Lean_Doc_argValToParser(v___x_1132_);
v___x_1135_ = lean_unsigned_to_nat(3u);
v___x_1136_ = lean_mk_empty_array_with_capacity(v___x_1135_);
v___x_1137_ = lean_array_push(v___x_1136_, v___x_1127_);
v___x_1138_ = lean_array_push(v___x_1137_, v_eq_1130_);
v___x_1139_ = lean_array_push(v___x_1138_, v___x_1134_);
v___x_1140_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1133_, v___x_1139_);
return v___x_1140_;
}
}
}
else
{
lean_object* v___x_1143_; lean_object* v_po_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v_po_1144_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1143_);
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1145_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v___x_1146_);
v___x_1165_ = l_Lean_Syntax_isOfKind(v___x_1146_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_dec(v___x_1146_);
lean_dec(v_po_1144_);
return v_stx_1089_;
}
else
{
goto v___jp_1147_;
}
}
else
{
goto v___jp_1147_;
}
v___jp_1147_:
{
lean_object* v___x_1148_; lean_object* v_eq_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_pc_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1148_ = lean_unsigned_to_nat(2u);
v_eq_1149_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(3u);
v___x_1151_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1150_);
v___x_1152_ = lean_unsigned_to_nat(4u);
v_pc_1153_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1152_);
lean_dec(v_stx_1089_);
v___x_1154_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__4));
v___x_1155_ = l_Lean_Doc_argValToParser(v___x_1151_);
v___x_1156_ = lean_unsigned_to_nat(5u);
v___x_1157_ = lean_mk_empty_array_with_capacity(v___x_1156_);
v___x_1158_ = lean_array_push(v___x_1157_, v_po_1144_);
v___x_1159_ = lean_array_push(v___x_1158_, v___x_1146_);
v___x_1160_ = lean_array_push(v___x_1159_, v_eq_1149_);
v___x_1161_ = lean_array_push(v___x_1160_, v___x_1155_);
v___x_1162_ = lean_array_push(v___x_1161_, v_pc_1153_);
v___x_1163_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1154_, v___x_1162_);
return v___x_1163_;
}
}
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = l_Lean_Syntax_getArg(v_stx_1089_, v___x_1166_);
lean_dec(v_stx_1089_);
v___x_1168_ = ((lean_object*)(l_Lean_Doc_ArgView_of___closed__2));
v___x_1169_ = l_Lean_Doc_argValToParser(v___x_1167_);
v___x_1170_ = lean_unsigned_to_nat(1u);
v___x_1171_ = lean_mk_empty_array_with_capacity(v___x_1170_);
v___x_1172_ = lean_array_push(v___x_1171_, v___x_1169_);
v___x_1173_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1168_, v___x_1172_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_linkTargetToParser(lean_object* v_stx_1199_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__1));
lean_inc(v_stx_1199_);
v___x_1201_ = l_Lean_Syntax_isOfKind(v_stx_1199_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__3));
lean_inc(v_stx_1199_);
v___x_1203_ = l_Lean_Syntax_isOfKind(v_stx_1199_, v___x_1202_);
if (v___x_1203_ == 0)
{
return v_stx_1199_;
}
else
{
lean_object* v___x_1204_; lean_object* v_o_1205_; lean_object* v___x_1206_; lean_object* v_name_1207_; lean_object* v___x_1208_; lean_object* v_c_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v_o_1205_ = l_Lean_Syntax_getArg(v_stx_1199_, v___x_1204_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v_name_1207_ = l_Lean_Syntax_getArg(v_stx_1199_, v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(2u);
v_c_1209_ = l_Lean_Syntax_getArg(v_stx_1199_, v___x_1208_);
lean_dec(v_stx_1199_);
v___x_1210_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__5));
v___x_1211_ = l_Lean_TSyntax_getString(v_name_1207_);
v___x_1212_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_1207_, v___x_1211_, v___x_1201_);
lean_dec(v_name_1207_);
v___x_1213_ = lean_unsigned_to_nat(3u);
v___x_1214_ = lean_mk_empty_array_with_capacity(v___x_1213_);
v___x_1215_ = lean_array_push(v___x_1214_, v_o_1205_);
v___x_1216_ = lean_array_push(v___x_1215_, v___x_1212_);
v___x_1217_ = lean_array_push(v___x_1216_, v_c_1209_);
v___x_1218_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1210_, v___x_1217_);
return v___x_1218_;
}
}
else
{
lean_object* v___x_1219_; lean_object* v_o_1220_; lean_object* v___x_1221_; lean_object* v_url_1222_; lean_object* v___x_1223_; lean_object* v_c_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v_o_1220_ = l_Lean_Syntax_getArg(v_stx_1199_, v___x_1219_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v_url_1222_ = l_Lean_Syntax_getArg(v_stx_1199_, v___x_1221_);
v___x_1223_ = lean_unsigned_to_nat(2u);
v_c_1224_ = l_Lean_Syntax_getArg(v_stx_1199_, v___x_1223_);
lean_dec(v_stx_1199_);
v___x_1225_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__6));
v___x_1226_ = l_Lean_TSyntax_getString(v_url_1222_);
v___x_1227_ = 0;
v___x_1228_ = l_Lean_Doc_mkVersoLinkUrlFrom(v_url_1222_, v___x_1226_, v___x_1227_);
lean_dec(v_url_1222_);
v___x_1229_ = lean_unsigned_to_nat(3u);
v___x_1230_ = lean_mk_empty_array_with_capacity(v___x_1229_);
v___x_1231_ = lean_array_push(v___x_1230_, v_o_1220_);
v___x_1232_ = lean_array_push(v___x_1231_, v___x_1228_);
v___x_1233_ = lean_array_push(v___x_1232_, v_c_1224_);
v___x_1234_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1225_, v___x_1233_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(lean_object* v_o_1242_, lean_object* v_s_1243_, lean_object* v_c_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
v___x_1246_ = l_Lean_TSyntax_getString(v_s_1243_);
lean_inc_ref_n(v___x_1246_, 2);
v___x_1247_ = l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(v___x_1246_, v_o_1242_);
v___x_1248_ = 0;
v___x_1249_ = l_Lean_Doc_mkVersoCodeFrom(v_s_1243_, v___x_1246_, v___x_1248_);
v___x_1250_ = l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter(v___x_1246_, v_c_1244_);
v___x_1251_ = lean_unsigned_to_nat(3u);
v___x_1252_ = lean_mk_empty_array_with_capacity(v___x_1251_);
v___x_1253_ = lean_array_push(v___x_1252_, v___x_1247_);
v___x_1254_ = lean_array_push(v___x_1253_, v___x_1249_);
v___x_1255_ = lean_array_push(v___x_1254_, v___x_1250_);
v___x_1256_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1245_, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___boxed(lean_object* v_o_1257_, lean_object* v_s_1258_, lean_object* v_c_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1257_, v_s_1258_, v_c_1259_);
lean_dec(v_c_1259_);
lean_dec(v_s_1258_);
lean_dec(v_o_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(size_t v_sz_1261_, size_t v_i_1262_, lean_object* v_bs_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_usize_dec_lt(v_i_1262_, v_sz_1261_);
if (v___x_1264_ == 0)
{
return v_bs_1263_;
}
else
{
lean_object* v_v_1265_; lean_object* v___x_1266_; lean_object* v_bs_x27_1267_; lean_object* v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; lean_object* v___x_1271_; 
v_v_1265_ = lean_array_uget(v_bs_1263_, v_i_1262_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v_bs_x27_1267_ = lean_array_uset(v_bs_1263_, v_i_1262_, v___x_1266_);
v___x_1268_ = l_Lean_Doc_docArgToParser(v_v_1265_);
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_add(v_i_1262_, v___x_1269_);
v___x_1271_ = lean_array_uset(v_bs_x27_1267_, v_i_1262_, v___x_1268_);
v_i_1262_ = v___x_1270_;
v_bs_1263_ = v___x_1271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0___boxed(lean_object* v_sz_1273_, lean_object* v_i_1274_, lean_object* v_bs_1275_){
_start:
{
size_t v_sz_boxed_1276_; size_t v_i_boxed_1277_; lean_object* v_res_1278_; 
v_sz_boxed_1276_ = lean_unbox_usize(v_sz_1273_);
lean_dec(v_sz_1273_);
v_i_boxed_1277_ = lean_unbox_usize(v_i_1274_);
lean_dec(v_i_1274_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_boxed_1276_, v_i_boxed_1277_, v_bs_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_inlineToParser(lean_object* v_stx_1431_){
_start:
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__1));
lean_inc(v_stx_1431_);
v___x_1433_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__3));
lean_inc(v_stx_1431_);
v___x_1435_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__5));
lean_inc(v_stx_1431_);
v___x_1437_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__6));
lean_inc(v_stx_1431_);
v___x_1439_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__8));
lean_inc(v_stx_1431_);
v___x_1441_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1442_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__10));
lean_inc(v_stx_1431_);
v___x_1443_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__12));
lean_inc(v_stx_1431_);
v___x_1445_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__14));
lean_inc(v_stx_1431_);
v___x_1447_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__16));
lean_inc(v_stx_1431_);
v___x_1449_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__17));
lean_inc(v_stx_1431_);
v___x_1451_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; uint8_t v___x_1453_; 
v___x_1452_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__19));
lean_inc(v_stx_1431_);
v___x_1453_ = l_Lean_Syntax_isOfKind(v_stx_1431_, v___x_1452_);
if (v___x_1453_ == 0)
{
return v_stx_1431_;
}
else
{
lean_object* v___x_1454_; lean_object* v_bo_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v_bc_1461_; lean_object* v___x_1462_; lean_object* v_so_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_sc_1467_; lean_object* v_inl_1468_; lean_object* v_args_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; size_t v_sz_1473_; size_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v_bo_1455_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1454_);
v___x_1456_ = lean_unsigned_to_nat(1u);
v___x_1457_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1456_);
v___x_1458_ = lean_unsigned_to_nat(2u);
v___x_1459_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1458_);
v___x_1460_ = lean_unsigned_to_nat(3u);
v_bc_1461_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1460_);
v___x_1462_ = lean_unsigned_to_nat(4u);
v_so_1463_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1462_);
v___x_1464_ = lean_unsigned_to_nat(5u);
v___x_1465_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1464_);
v___x_1466_ = lean_unsigned_to_nat(6u);
v_sc_1467_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1466_);
lean_dec(v_stx_1431_);
v_inl_1468_ = l_Lean_Syntax_getArgs(v___x_1465_);
lean_dec(v___x_1465_);
v_args_1469_ = l_Lean_Syntax_getArgs(v___x_1459_);
lean_dec(v___x_1459_);
v___x_1470_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__20));
v___x_1471_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__21));
v___x_1472_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1471_, v_bo_1455_);
lean_dec(v_bo_1455_);
v_sz_1473_ = lean_array_size(v_args_1469_);
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_1473_, v___x_1474_, v_args_1469_);
v___x_1476_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_1477_ = lean_box(2);
v___x_1478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
lean_ctor_set(v___x_1478_, 2, v___x_1475_);
v___x_1479_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__22));
v___x_1480_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1479_, v_bc_1461_);
lean_dec(v_bc_1461_);
v___x_1481_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__23));
v___x_1482_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1481_, v_so_1463_);
lean_dec(v_so_1463_);
v___x_1483_ = lean_mk_empty_array_with_capacity(v___x_1456_);
lean_inc_ref(v___x_1483_);
v___x_1484_ = lean_array_push(v___x_1483_, v___x_1482_);
v___x_1485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1477_);
lean_ctor_set(v___x_1485_, 1, v___x_1476_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
v___x_1486_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1468_);
v___x_1487_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1488_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1487_, v_sc_1467_);
lean_dec(v_sc_1467_);
v___x_1489_ = lean_array_push(v___x_1483_, v___x_1488_);
v___x_1490_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1477_);
lean_ctor_set(v___x_1490_, 1, v___x_1476_);
lean_ctor_set(v___x_1490_, 2, v___x_1489_);
v___x_1491_ = lean_unsigned_to_nat(7u);
v___x_1492_ = lean_mk_empty_array_with_capacity(v___x_1491_);
v___x_1493_ = lean_array_push(v___x_1492_, v___x_1472_);
v___x_1494_ = lean_array_push(v___x_1493_, v___x_1457_);
v___x_1495_ = lean_array_push(v___x_1494_, v___x_1478_);
v___x_1496_ = lean_array_push(v___x_1495_, v___x_1480_);
v___x_1497_ = lean_array_push(v___x_1496_, v___x_1485_);
v___x_1498_ = lean_array_push(v___x_1497_, v___x_1486_);
v___x_1499_ = lean_array_push(v___x_1498_, v___x_1490_);
v___x_1500_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1470_, v___x_1499_);
return v___x_1500_;
}
}
else
{
lean_object* v___x_1501_; lean_object* v_s_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1501_ = lean_unsigned_to_nat(1u);
v_s_1502_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1501_);
lean_dec(v_stx_1431_);
v___x_1503_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
v___x_1504_ = l___private_Lean_DocString_View_0__Lean_Doc_decodedInfo(v_s_1502_);
v___x_1505_ = l_Lean_TSyntax_getString(v_s_1502_);
lean_dec(v_s_1502_);
v___x_1506_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = lean_mk_empty_array_with_capacity(v___x_1501_);
v___x_1508_ = lean_array_push(v___x_1507_, v___x_1506_);
v___x_1509_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1503_, v___x_1508_);
return v___x_1509_;
}
}
else
{
lean_object* v___x_1510_; lean_object* v_o_1511_; lean_object* v___x_1512_; lean_object* v_name_1513_; lean_object* v___x_1514_; lean_object* v_c_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1510_ = lean_unsigned_to_nat(0u);
v_o_1511_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1510_);
v___x_1512_ = lean_unsigned_to_nat(1u);
v_name_1513_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1512_);
v___x_1514_ = lean_unsigned_to_nat(2u);
v_c_1515_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1514_);
lean_dec(v_stx_1431_);
v___x_1516_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__25));
v___x_1517_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__26));
v___x_1518_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1517_, v_o_1511_);
lean_dec(v_o_1511_);
v___x_1519_ = l_Lean_TSyntax_getString(v_name_1513_);
v___x_1520_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_1513_, v___x_1519_, v___x_1447_);
lean_dec(v_name_1513_);
v___x_1521_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1522_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1521_, v_c_1515_);
lean_dec(v_c_1515_);
v___x_1523_ = lean_unsigned_to_nat(3u);
v___x_1524_ = lean_mk_empty_array_with_capacity(v___x_1523_);
v___x_1525_ = lean_array_push(v___x_1524_, v___x_1518_);
v___x_1526_ = lean_array_push(v___x_1525_, v___x_1520_);
v___x_1527_ = lean_array_push(v___x_1526_, v___x_1522_);
v___x_1528_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1516_, v___x_1527_);
return v___x_1528_;
}
}
else
{
lean_object* v___x_1529_; lean_object* v_o_1530_; lean_object* v___x_1531_; lean_object* v_alt_1532_; lean_object* v___x_1533_; lean_object* v_c_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1529_ = lean_unsigned_to_nat(0u);
v_o_1530_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1529_);
v___x_1531_ = lean_unsigned_to_nat(1u);
v_alt_1532_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1531_);
v___x_1533_ = lean_unsigned_to_nat(2u);
v_c_1534_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1533_);
v___x_1535_ = lean_unsigned_to_nat(3u);
v___x_1536_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1535_);
lean_dec(v_stx_1431_);
v___x_1537_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__27));
v___x_1538_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__28));
v___x_1539_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1538_, v_o_1530_);
lean_dec(v_o_1530_);
v___x_1540_ = l_Lean_TSyntax_getString(v_alt_1532_);
v___x_1541_ = l_Lean_Doc_mkVersoImageAltFrom(v_alt_1532_, v___x_1540_, v___x_1445_);
lean_dec(v_alt_1532_);
v___x_1542_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1543_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1542_, v_c_1534_);
lean_dec(v_c_1534_);
v___x_1544_ = l_Lean_Doc_linkTargetToParser(v___x_1536_);
v___x_1545_ = lean_unsigned_to_nat(4u);
v___x_1546_ = lean_mk_empty_array_with_capacity(v___x_1545_);
v___x_1547_ = lean_array_push(v___x_1546_, v___x_1539_);
v___x_1548_ = lean_array_push(v___x_1547_, v___x_1541_);
v___x_1549_ = lean_array_push(v___x_1548_, v___x_1543_);
v___x_1550_ = lean_array_push(v___x_1549_, v___x_1544_);
v___x_1551_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1537_, v___x_1550_);
return v___x_1551_;
}
}
else
{
lean_object* v___x_1552_; lean_object* v_o_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_c_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v_inl_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1552_ = lean_unsigned_to_nat(0u);
v_o_1553_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1552_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1554_);
v___x_1556_ = lean_unsigned_to_nat(2u);
v_c_1557_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1556_);
v___x_1558_ = lean_unsigned_to_nat(3u);
v___x_1559_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1558_);
lean_dec(v_stx_1431_);
v_inl_1560_ = l_Lean_Syntax_getArgs(v___x_1555_);
lean_dec(v___x_1555_);
v___x_1561_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__29));
v___x_1562_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__23));
v___x_1563_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1562_, v_o_1553_);
lean_dec(v_o_1553_);
v___x_1564_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1560_);
v___x_1565_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__24));
v___x_1566_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_1565_, v_c_1557_);
lean_dec(v_c_1557_);
v___x_1567_ = l_Lean_Doc_linkTargetToParser(v___x_1559_);
v___x_1568_ = lean_unsigned_to_nat(4u);
v___x_1569_ = lean_mk_empty_array_with_capacity(v___x_1568_);
v___x_1570_ = lean_array_push(v___x_1569_, v___x_1563_);
v___x_1571_ = lean_array_push(v___x_1570_, v___x_1564_);
v___x_1572_ = lean_array_push(v___x_1571_, v___x_1566_);
v___x_1573_ = lean_array_push(v___x_1572_, v___x_1567_);
v___x_1574_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1561_, v___x_1573_);
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1575_ = lean_unsigned_to_nat(1u);
v___x_1576_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1575_);
lean_inc(v___x_1576_);
v___x_1577_ = l_Lean_Syntax_isOfKind(v___x_1576_, v___x_1438_);
if (v___x_1577_ == 0)
{
lean_dec(v___x_1576_);
return v_stx_1431_;
}
else
{
lean_object* v___x_1578_; lean_object* v_m_1579_; lean_object* v_o_1580_; lean_object* v_s_1581_; lean_object* v___x_1582_; lean_object* v_c_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v_m_1579_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1578_);
lean_dec(v_stx_1431_);
v_o_1580_ = l_Lean_Syntax_getArg(v___x_1576_, v___x_1578_);
v_s_1581_ = l_Lean_Syntax_getArg(v___x_1576_, v___x_1575_);
v___x_1582_ = lean_unsigned_to_nat(2u);
v_c_1583_ = l_Lean_Syntax_getArg(v___x_1576_, v___x_1582_);
lean_dec(v___x_1576_);
v___x_1584_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__30));
v___x_1585_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__32));
v___x_1586_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__33));
v___x_1587_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1585_, v___x_1586_, v_m_1579_);
lean_dec(v_m_1579_);
v___x_1588_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1580_, v_s_1581_, v_c_1583_);
lean_dec(v_c_1583_);
lean_dec(v_s_1581_);
lean_dec(v_o_1580_);
v___x_1589_ = lean_mk_empty_array_with_capacity(v___x_1582_);
v___x_1590_ = lean_array_push(v___x_1589_, v___x_1587_);
v___x_1591_ = lean_array_push(v___x_1590_, v___x_1588_);
v___x_1592_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1584_, v___x_1591_);
return v___x_1592_;
}
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1593_);
lean_inc(v___x_1594_);
v___x_1595_ = l_Lean_Syntax_isOfKind(v___x_1594_, v___x_1438_);
if (v___x_1595_ == 0)
{
lean_dec(v___x_1594_);
return v_stx_1431_;
}
else
{
lean_object* v___x_1596_; lean_object* v_m_1597_; lean_object* v_o_1598_; lean_object* v_s_1599_; lean_object* v___x_1600_; lean_object* v_c_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1596_ = lean_unsigned_to_nat(0u);
v_m_1597_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1596_);
lean_dec(v_stx_1431_);
v_o_1598_ = l_Lean_Syntax_getArg(v___x_1594_, v___x_1596_);
v_s_1599_ = l_Lean_Syntax_getArg(v___x_1594_, v___x_1593_);
v___x_1600_ = lean_unsigned_to_nat(2u);
v_c_1601_ = l_Lean_Syntax_getArg(v___x_1594_, v___x_1600_);
lean_dec(v___x_1594_);
v___x_1602_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__34));
v___x_1603_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__36));
v___x_1604_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__37));
v___x_1605_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1603_, v___x_1604_, v_m_1597_);
lean_dec(v_m_1597_);
v___x_1606_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1598_, v_s_1599_, v_c_1601_);
lean_dec(v_c_1601_);
lean_dec(v_s_1599_);
lean_dec(v_o_1598_);
v___x_1607_ = lean_mk_empty_array_with_capacity(v___x_1600_);
v___x_1608_ = lean_array_push(v___x_1607_, v___x_1605_);
v___x_1609_ = lean_array_push(v___x_1608_, v___x_1606_);
v___x_1610_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1602_, v___x_1609_);
return v___x_1610_;
}
}
}
else
{
lean_object* v___x_1611_; lean_object* v_o_1612_; lean_object* v___x_1613_; lean_object* v_s_1614_; lean_object* v___x_1615_; lean_object* v_c_1616_; lean_object* v___x_1617_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
v_o_1612_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1611_);
v___x_1613_ = lean_unsigned_to_nat(1u);
v_s_1614_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1613_);
v___x_1615_ = lean_unsigned_to_nat(2u);
v_c_1616_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1615_);
lean_dec(v_stx_1431_);
v___x_1617_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code(v_o_1612_, v_s_1614_, v_c_1616_);
lean_dec(v_c_1616_);
lean_dec(v_s_1614_);
lean_dec(v_o_1612_);
return v___x_1617_;
}
}
else
{
lean_object* v___x_1618_; lean_object* v_o_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v_c_1623_; lean_object* v_inl_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v_o_1619_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1618_);
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1620_);
v___x_1622_ = lean_unsigned_to_nat(2u);
v_c_1623_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1622_);
lean_dec(v_stx_1431_);
v_inl_1624_ = l_Lean_Syntax_getArgs(v___x_1621_);
lean_dec(v___x_1621_);
v___x_1625_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__38));
v___x_1626_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__40));
v___x_1627_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__41));
v___x_1628_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1626_, v___x_1627_, v_o_1619_);
lean_dec(v_o_1619_);
v___x_1629_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1624_);
v___x_1630_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1626_, v___x_1627_, v_c_1623_);
lean_dec(v_c_1623_);
v___x_1631_ = lean_unsigned_to_nat(3u);
v___x_1632_ = lean_mk_empty_array_with_capacity(v___x_1631_);
v___x_1633_ = lean_array_push(v___x_1632_, v___x_1628_);
v___x_1634_ = lean_array_push(v___x_1633_, v___x_1629_);
v___x_1635_ = lean_array_push(v___x_1634_, v___x_1630_);
v___x_1636_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1625_, v___x_1635_);
return v___x_1636_;
}
}
else
{
lean_object* v___x_1637_; lean_object* v_o_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_c_1642_; lean_object* v_inl_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
v_o_1638_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1637_);
v___x_1639_ = lean_unsigned_to_nat(1u);
v___x_1640_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1639_);
v___x_1641_ = lean_unsigned_to_nat(2u);
v_c_1642_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1641_);
lean_dec(v_stx_1431_);
v_inl_1643_ = l_Lean_Syntax_getArgs(v___x_1640_);
lean_dec(v___x_1640_);
v___x_1644_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__42));
v___x_1645_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__44));
v___x_1646_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__45));
v___x_1647_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1645_, v___x_1646_, v_o_1638_);
lean_dec(v_o_1638_);
v___x_1648_ = l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(v_inl_1643_);
v___x_1649_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1645_, v___x_1646_, v_c_1642_);
lean_dec(v_c_1642_);
v___x_1650_ = lean_unsigned_to_nat(3u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_array_push(v___x_1651_, v___x_1647_);
v___x_1653_ = lean_array_push(v___x_1652_, v___x_1648_);
v___x_1654_ = lean_array_push(v___x_1653_, v___x_1649_);
v___x_1655_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1644_, v___x_1654_);
return v___x_1655_;
}
}
else
{
lean_object* v___x_1656_; lean_object* v_s_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1656_ = lean_unsigned_to_nat(0u);
v_s_1657_ = l_Lean_Syntax_getArg(v_stx_1431_, v___x_1656_);
v___x_1658_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__10));
lean_inc(v_s_1657_);
v___x_1659_ = l_Lean_Syntax_isOfKind(v_s_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_dec(v_s_1657_);
return v_stx_1431_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec(v_stx_1431_);
v___x_1660_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__46));
v___x_1661_ = l_Lean_TSyntax_getString(v_s_1657_);
v___x_1662_ = 0;
v___x_1663_ = l_Lean_Doc_mkVersoTextFrom(v_s_1657_, v___x_1661_, v___x_1662_);
lean_dec(v_s_1657_);
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_mk_empty_array_with_capacity(v___x_1664_);
v___x_1666_ = lean_array_push(v___x_1665_, v___x_1663_);
v___x_1667_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1660_, v___x_1666_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(size_t v_sz_1668_, size_t v_i_1669_, lean_object* v_bs_1670_){
_start:
{
uint8_t v___x_1671_; 
v___x_1671_ = lean_usize_dec_lt(v_i_1669_, v_sz_1668_);
if (v___x_1671_ == 0)
{
return v_bs_1670_;
}
else
{
lean_object* v_v_1672_; lean_object* v___x_1673_; lean_object* v_bs_x27_1674_; lean_object* v___x_1675_; size_t v___x_1676_; size_t v___x_1677_; lean_object* v___x_1678_; 
v_v_1672_ = lean_array_uget(v_bs_1670_, v_i_1669_);
v___x_1673_ = lean_unsigned_to_nat(0u);
v_bs_x27_1674_ = lean_array_uset(v_bs_1670_, v_i_1669_, v___x_1673_);
v___x_1675_ = l_Lean_Doc_inlineToParser(v_v_1672_);
v___x_1676_ = ((size_t)1ULL);
v___x_1677_ = lean_usize_add(v_i_1669_, v___x_1676_);
v___x_1678_ = lean_array_uset(v_bs_x27_1674_, v_i_1669_, v___x_1675_);
v_i_1669_ = v___x_1677_;
v_bs_1670_ = v___x_1678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines(lean_object* v_inl_1680_){
_start:
{
size_t v_sz_1681_; size_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v_sz_1681_ = lean_array_size(v_inl_1680_);
v___x_1682_ = ((size_t)0ULL);
v___x_1683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_1681_, v___x_1682_, v_inl_1680_);
v___x_1684_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_1685_ = lean_box(2);
v___x_1686_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
lean_ctor_set(v___x_1686_, 2, v___x_1683_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2___boxed(lean_object* v_sz_1687_, lean_object* v_i_1688_, lean_object* v_bs_1689_){
_start:
{
size_t v_sz_boxed_1690_; size_t v_i_boxed_1691_; lean_object* v_res_1692_; 
v_sz_boxed_1690_ = lean_unbox_usize(v_sz_1687_);
lean_dec(v_sz_1687_);
v_i_boxed_1691_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_res_1692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_boxed_1690_, v_i_boxed_1691_, v_bs_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_blockToParser_spec__2(lean_object* v_x_1693_, lean_object* v_x_1694_){
_start:
{
lean_object* v_zero_1695_; uint8_t v_isZero_1696_; 
v_zero_1695_ = lean_unsigned_to_nat(0u);
v_isZero_1696_ = lean_nat_dec_eq(v_x_1693_, v_zero_1695_);
if (v_isZero_1696_ == 1)
{
lean_dec(v_x_1693_);
return v_x_1694_;
}
else
{
uint32_t v___x_1697_; lean_object* v_one_1698_; lean_object* v_n_1699_; lean_object* v___x_1700_; 
v___x_1697_ = 35;
v_one_1698_ = lean_unsigned_to_nat(1u);
v_n_1699_ = lean_nat_sub(v_x_1693_, v_one_1698_);
lean_dec(v_x_1693_);
v___x_1700_ = lean_string_push(v_x_1694_, v___x_1697_);
v_x_1693_ = v_n_1699_;
v_x_1694_ = v___x_1700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_descItemToParser(lean_object* v_stx_1856_){
_start:
{
lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_Doc_descItemToParser___closed__1));
lean_inc(v_stx_1856_);
v___x_1858_ = l_Lean_Syntax_isOfKind(v_stx_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
return v_stx_1856_;
}
else
{
lean_object* v___x_1859_; lean_object* v_marker_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v_desc_1865_; lean_object* v_term_1866_; lean_object* v___x_1867_; size_t v_sz_1868_; size_t v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; size_t v_sz_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v_marker_1860_ = l_Lean_Syntax_getArg(v_stx_1856_, v___x_1859_);
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = l_Lean_Syntax_getArg(v_stx_1856_, v___x_1861_);
v___x_1863_ = lean_unsigned_to_nat(3u);
v___x_1864_ = l_Lean_Syntax_getArg(v_stx_1856_, v___x_1863_);
lean_dec(v_stx_1856_);
v_desc_1865_ = l_Lean_Syntax_getArgs(v___x_1864_);
lean_dec(v___x_1864_);
v_term_1866_ = l_Lean_Syntax_getArgs(v___x_1862_);
lean_dec(v___x_1862_);
v___x_1867_ = ((lean_object*)(l_Lean_Doc_descItemToParser___closed__3));
v_sz_1868_ = lean_array_size(v_term_1866_);
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_1868_, v___x_1869_, v_term_1866_);
v___x_1871_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_1872_ = lean_box(2);
v___x_1873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1871_);
lean_ctor_set(v___x_1873_, 2, v___x_1870_);
v_sz_1874_ = lean_array_size(v_desc_1865_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_1874_, v___x_1869_, v_desc_1865_);
v___x_1876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1872_);
lean_ctor_set(v___x_1876_, 1, v___x_1871_);
lean_ctor_set(v___x_1876_, 2, v___x_1875_);
v___x_1877_ = lean_mk_empty_array_with_capacity(v___x_1863_);
v___x_1878_ = lean_array_push(v___x_1877_, v_marker_1860_);
v___x_1879_ = lean_array_push(v___x_1878_, v___x_1873_);
v___x_1880_ = lean_array_push(v___x_1879_, v___x_1876_);
v___x_1881_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1867_, v___x_1880_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(size_t v_sz_1882_, size_t v_i_1883_, lean_object* v_bs_1884_){
_start:
{
uint8_t v___x_1885_; 
v___x_1885_ = lean_usize_dec_lt(v_i_1883_, v_sz_1882_);
if (v___x_1885_ == 0)
{
return v_bs_1884_;
}
else
{
lean_object* v_v_1886_; lean_object* v___x_1887_; lean_object* v_bs_x27_1888_; lean_object* v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; lean_object* v___x_1892_; 
v_v_1886_ = lean_array_uget(v_bs_1884_, v_i_1883_);
v___x_1887_ = lean_unsigned_to_nat(0u);
v_bs_x27_1888_ = lean_array_uset(v_bs_1884_, v_i_1883_, v___x_1887_);
v___x_1889_ = l_Lean_Doc_descItemToParser(v_v_1886_);
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_add(v_i_1883_, v___x_1890_);
v___x_1892_ = lean_array_uset(v_bs_x27_1888_, v_i_1883_, v___x_1889_);
v_i_1883_ = v___x_1891_;
v_bs_1884_ = v___x_1892_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_listItemToParser(lean_object* v_marker_1914_, lean_object* v_stx_1915_){
_start:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__1));
lean_inc(v_stx_1915_);
v___x_1917_ = l_Lean_Syntax_isOfKind(v_stx_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec_ref(v_marker_1914_);
return v_stx_1915_;
}
else
{
lean_object* v___x_1918_; lean_object* v_m_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_bs_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; size_t v_sz_1926_; size_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1918_ = lean_unsigned_to_nat(0u);
v_m_1919_ = l_Lean_Syntax_getArg(v_stx_1915_, v___x_1918_);
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = l_Lean_Syntax_getArg(v_stx_1915_, v___x_1920_);
lean_dec(v_stx_1915_);
v_bs_1922_ = l_Lean_Syntax_getArgs(v___x_1921_);
lean_dec(v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__4));
v___x_1924_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__6));
v___x_1925_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_1924_, v_marker_1914_, v_m_1919_);
lean_dec(v_m_1919_);
v_sz_1926_ = lean_array_size(v_bs_1922_);
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_1926_, v___x_1927_, v_bs_1922_);
v___x_1929_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_1930_ = lean_box(2);
v___x_1931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v___x_1929_);
lean_ctor_set(v___x_1931_, 2, v___x_1928_);
v___x_1932_ = lean_unsigned_to_nat(2u);
v___x_1933_ = lean_mk_empty_array_with_capacity(v___x_1932_);
v___x_1934_ = lean_array_push(v___x_1933_, v___x_1925_);
v___x_1935_ = lean_array_push(v___x_1934_, v___x_1931_);
v___x_1936_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_1923_, v___x_1935_);
return v___x_1936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(lean_object* v_n_1937_, size_t v_sz_1938_, size_t v_i_1939_, lean_object* v_bs_1940_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1939_, v_sz_1938_);
if (v___x_1941_ == 0)
{
return v_bs_1940_;
}
else
{
lean_object* v_v_1942_; lean_object* v___x_1943_; lean_object* v_bs_x27_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; lean_object* v___x_1954_; 
v_v_1942_ = lean_array_uget(v_bs_1940_, v_i_1939_);
v___x_1943_ = lean_unsigned_to_nat(0u);
v_bs_x27_1944_ = lean_array_uset(v_bs_1940_, v_i_1939_, v___x_1943_);
v___x_1945_ = lean_usize_to_nat(v_i_1939_);
v___x_1946_ = l_Lean_TSyntax_getNat(v_n_1937_);
v___x_1947_ = lean_nat_add(v___x_1946_, v___x_1945_);
lean_dec(v___x_1945_);
lean_dec(v___x_1946_);
v___x_1948_ = l_Nat_reprFast(v___x_1947_);
v___x_1949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___closed__0));
v___x_1950_ = lean_string_append(v___x_1948_, v___x_1949_);
v___x_1951_ = l_Lean_Doc_listItemToParser(v___x_1950_, v_v_1942_);
v___x_1952_ = ((size_t)1ULL);
v___x_1953_ = lean_usize_add(v_i_1939_, v___x_1952_);
v___x_1954_ = lean_array_uset(v_bs_x27_1944_, v_i_1939_, v___x_1951_);
v_i_1939_ = v___x_1953_;
v_bs_1940_ = v___x_1954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(size_t v_sz_1968_, size_t v_i_1969_, lean_object* v_bs_1970_){
_start:
{
uint8_t v___x_1971_; 
v___x_1971_ = lean_usize_dec_lt(v_i_1969_, v_sz_1968_);
if (v___x_1971_ == 0)
{
return v_bs_1970_;
}
else
{
lean_object* v_v_1972_; lean_object* v___x_1973_; lean_object* v_bs_x27_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; lean_object* v___x_1979_; 
v_v_1972_ = lean_array_uget(v_bs_1970_, v_i_1969_);
v___x_1973_ = lean_unsigned_to_nat(0u);
v_bs_x27_1974_ = lean_array_uset(v_bs_1970_, v_i_1969_, v___x_1973_);
v___x_1975_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__41));
v___x_1976_ = l_Lean_Doc_listItemToParser(v___x_1975_, v_v_1972_);
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1969_, v___x_1977_);
v___x_1979_ = lean_array_uset(v_bs_x27_1974_, v_i_1969_, v___x_1976_);
v_i_1969_ = v___x_1978_;
v_bs_1970_ = v___x_1979_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_blockToParser(lean_object* v_stx_1993_){
_start:
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__1));
lean_inc(v_stx_1993_);
v___x_1995_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__3));
lean_inc(v_stx_1993_);
v___x_1997_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__5));
lean_inc(v_stx_1993_);
v___x_1999_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__7));
lean_inc(v_stx_1993_);
v___x_2001_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__9));
lean_inc(v_stx_1993_);
v___x_2003_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2002_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__11));
lean_inc(v_stx_1993_);
v___x_2005_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__13));
lean_inc(v_stx_1993_);
v___x_2007_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__15));
lean_inc(v_stx_1993_);
v___x_2009_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__17));
lean_inc(v_stx_1993_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__19));
lean_inc(v_stx_1993_);
v___x_2013_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__21));
lean_inc(v_stx_1993_);
v___x_2015_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__23));
lean_inc(v_stx_1993_);
v___x_2017_ = l_Lean_Syntax_isOfKind(v_stx_1993_, v___x_2016_);
if (v___x_2017_ == 0)
{
return v_stx_1993_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__26));
lean_inc(v___x_2019_);
v___x_2021_ = l_Lean_Syntax_isOfKind(v___x_2019_, v___x_2020_);
if (v___x_2021_ == 0)
{
lean_dec(v___x_2019_);
return v_stx_1993_;
}
else
{
lean_object* v___x_2022_; lean_object* v_o_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v_c_2026_; lean_object* v_contents_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2022_ = lean_unsigned_to_nat(0u);
v_o_2023_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2022_);
v___x_2024_ = l_Lean_Syntax_getArg(v___x_2019_, v___x_2022_);
lean_dec(v___x_2019_);
v___x_2025_ = lean_unsigned_to_nat(2u);
v_c_2026_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2025_);
lean_dec(v_stx_1993_);
v_contents_2027_ = l_Lean_Syntax_getArgs(v___x_2024_);
lean_dec(v___x_2024_);
v___x_2028_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__28));
v___x_2029_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_contents_2027_);
lean_dec_ref(v_contents_2027_);
v___x_2030_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2031_ = lean_box(2);
v___x_2032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_2030_);
lean_ctor_set(v___x_2032_, 2, v___x_2029_);
v___x_2033_ = lean_mk_empty_array_with_capacity(v___x_2018_);
v___x_2034_ = lean_array_push(v___x_2033_, v___x_2032_);
v___x_2035_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2020_, v___x_2034_);
v___x_2036_ = lean_unsigned_to_nat(3u);
v___x_2037_ = lean_mk_empty_array_with_capacity(v___x_2036_);
v___x_2038_ = lean_array_push(v___x_2037_, v_o_2023_);
v___x_2039_ = lean_array_push(v___x_2038_, v___x_2035_);
v___x_2040_ = lean_array_push(v___x_2039_, v_c_2026_);
v___x_2041_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2028_, v___x_2040_);
return v___x_2041_;
}
}
}
else
{
lean_object* v___x_2042_; lean_object* v_o_2043_; lean_object* v___x_2044_; lean_object* v_name_2045_; lean_object* v___x_2046_; lean_object* v_closer_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v_inls_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; size_t v_sz_2054_; size_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2042_ = lean_unsigned_to_nat(0u);
v_o_2043_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2042_);
v___x_2044_ = lean_unsigned_to_nat(1u);
v_name_2045_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2044_);
v___x_2046_ = lean_unsigned_to_nat(2u);
v_closer_2047_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2046_);
v___x_2048_ = lean_unsigned_to_nat(3u);
v___x_2049_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2048_);
lean_dec(v_stx_1993_);
v_inls_2050_ = l_Lean_Syntax_getArgs(v___x_2049_);
lean_dec(v___x_2049_);
v___x_2051_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__29));
v___x_2052_ = l_Lean_TSyntax_getString(v_name_2045_);
v___x_2053_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_2045_, v___x_2052_, v___x_2013_);
lean_dec(v_name_2045_);
v_sz_2054_ = lean_array_size(v_inls_2050_);
v___x_2055_ = ((size_t)0ULL);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_2054_, v___x_2055_, v_inls_2050_);
v___x_2057_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2058_ = lean_box(2);
v___x_2059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___x_2057_);
lean_ctor_set(v___x_2059_, 2, v___x_2056_);
v___x_2060_ = lean_unsigned_to_nat(4u);
v___x_2061_ = lean_mk_empty_array_with_capacity(v___x_2060_);
v___x_2062_ = lean_array_push(v___x_2061_, v_o_2043_);
v___x_2063_ = lean_array_push(v___x_2062_, v___x_2053_);
v___x_2064_ = lean_array_push(v___x_2063_, v_closer_2047_);
v___x_2065_ = lean_array_push(v___x_2064_, v___x_2059_);
v___x_2066_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2051_, v___x_2065_);
return v___x_2066_;
}
}
else
{
lean_object* v___x_2067_; lean_object* v_o_2068_; lean_object* v___x_2069_; lean_object* v_name_2070_; lean_object* v___x_2071_; lean_object* v_closer_2072_; lean_object* v___x_2073_; lean_object* v_url_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2067_ = lean_unsigned_to_nat(0u);
v_o_2068_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2067_);
v___x_2069_ = lean_unsigned_to_nat(1u);
v_name_2070_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2069_);
v___x_2071_ = lean_unsigned_to_nat(2u);
v_closer_2072_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2071_);
v___x_2073_ = lean_unsigned_to_nat(3u);
v_url_2074_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2073_);
lean_dec(v_stx_1993_);
v___x_2075_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__30));
v___x_2076_ = l_Lean_TSyntax_getString(v_name_2070_);
v___x_2077_ = l_Lean_Doc_mkVersoRefNameFrom(v_name_2070_, v___x_2076_, v___x_2011_);
lean_dec(v_name_2070_);
v___x_2078_ = l_Lean_TSyntax_getString(v_url_2074_);
v___x_2079_ = l_Lean_Doc_mkVersoLinkRefUrlFrom(v_url_2074_, v___x_2078_, v___x_2011_);
lean_dec(v_url_2074_);
v___x_2080_ = lean_unsigned_to_nat(4u);
v___x_2081_ = lean_mk_empty_array_with_capacity(v___x_2080_);
v___x_2082_ = lean_array_push(v___x_2081_, v_o_2068_);
v___x_2083_ = lean_array_push(v___x_2082_, v___x_2077_);
v___x_2084_ = lean_array_push(v___x_2083_, v_closer_2072_);
v___x_2085_ = lean_array_push(v___x_2084_, v___x_2079_);
v___x_2086_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2075_, v___x_2085_);
return v___x_2086_;
}
}
else
{
lean_object* v___x_2087_; lean_object* v_tok_2088_; lean_object* v___x_2089_; lean_object* v_n_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v_inls_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; size_t v_sz_2101_; size_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2087_ = lean_unsigned_to_nat(0u);
v_tok_2088_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2087_);
v___x_2089_ = lean_unsigned_to_nat(1u);
v_n_2090_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2089_);
v___x_2091_ = lean_unsigned_to_nat(4u);
v___x_2092_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2091_);
lean_dec(v_stx_1993_);
v_inls_2093_ = l_Lean_Syntax_getArgs(v___x_2092_);
lean_dec(v___x_2092_);
v___x_2094_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__31));
v___x_2095_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__33));
v___x_2096_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___x_2097_ = l_Lean_TSyntax_getNat(v_n_2090_);
lean_dec(v_n_2090_);
v___x_2098_ = lean_nat_add(v___x_2097_, v___x_2089_);
lean_dec(v___x_2097_);
v___x_2099_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Doc_blockToParser_spec__2(v___x_2098_, v___x_2096_);
v___x_2100_ = l___private_Lean_DocString_View_0__Lean_Doc_asDelimiter(v___x_2095_, v___x_2099_, v_tok_2088_);
lean_dec(v_tok_2088_);
v_sz_2101_ = lean_array_size(v_inls_2093_);
v___x_2102_ = ((size_t)0ULL);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_2101_, v___x_2102_, v_inls_2093_);
v___x_2104_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2105_ = lean_box(2);
v___x_2106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v___x_2104_);
lean_ctor_set(v___x_2106_, 2, v___x_2103_);
v___x_2107_ = lean_unsigned_to_nat(2u);
v___x_2108_ = lean_mk_empty_array_with_capacity(v___x_2107_);
v___x_2109_ = lean_array_push(v___x_2108_, v___x_2100_);
v___x_2110_ = lean_array_push(v___x_2109_, v___x_2106_);
v___x_2111_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2094_, v___x_2110_);
return v___x_2111_;
}
}
else
{
lean_object* v___x_2112_; lean_object* v_bo_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_bc_2119_; lean_object* v_args_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; size_t v_sz_2124_; size_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2112_ = lean_unsigned_to_nat(0u);
v_bo_2113_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2112_);
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2114_);
v___x_2116_ = lean_unsigned_to_nat(2u);
v___x_2117_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2116_);
v___x_2118_ = lean_unsigned_to_nat(3u);
v_bc_2119_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2118_);
lean_dec(v_stx_1993_);
v_args_2120_ = l_Lean_Syntax_getArgs(v___x_2117_);
lean_dec(v___x_2117_);
v___x_2121_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__34));
v___x_2122_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__21));
v___x_2123_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_2122_, v_bo_2113_);
lean_dec(v_bo_2113_);
v_sz_2124_ = lean_array_size(v_args_2120_);
v___x_2125_ = ((size_t)0ULL);
v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_2124_, v___x_2125_, v_args_2120_);
v___x_2127_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2128_ = lean_box(2);
v___x_2129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2127_);
lean_ctor_set(v___x_2129_, 2, v___x_2126_);
v___x_2130_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__22));
v___x_2131_ = l___private_Lean_DocString_View_0__Lean_Doc_asAtom(v___x_2130_, v_bc_2119_);
lean_dec(v_bc_2119_);
v___x_2132_ = lean_unsigned_to_nat(4u);
v___x_2133_ = lean_mk_empty_array_with_capacity(v___x_2132_);
v___x_2134_ = lean_array_push(v___x_2133_, v___x_2123_);
v___x_2135_ = lean_array_push(v___x_2134_, v___x_2115_);
v___x_2136_ = lean_array_push(v___x_2135_, v___x_2129_);
v___x_2137_ = lean_array_push(v___x_2136_, v___x_2131_);
v___x_2138_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2121_, v___x_2137_);
return v___x_2138_;
}
}
else
{
lean_object* v___x_2139_; lean_object* v_o_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_c_2148_; lean_object* v_bs_2149_; lean_object* v_args_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; size_t v_sz_2153_; size_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2139_ = lean_unsigned_to_nat(0u);
v_o_2140_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2139_);
v___x_2141_ = lean_unsigned_to_nat(1u);
v___x_2142_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2141_);
v___x_2143_ = lean_unsigned_to_nat(2u);
v___x_2144_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2143_);
v___x_2145_ = lean_unsigned_to_nat(4u);
v___x_2146_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2145_);
v___x_2147_ = lean_unsigned_to_nat(5u);
v_c_2148_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2147_);
lean_dec(v_stx_1993_);
v_bs_2149_ = l_Lean_Syntax_getArgs(v___x_2146_);
lean_dec(v___x_2146_);
v_args_2150_ = l_Lean_Syntax_getArgs(v___x_2144_);
lean_dec(v___x_2144_);
v___x_2151_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__35));
v___x_2152_ = l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(v_o_2140_);
lean_dec(v_o_2140_);
v_sz_2153_ = lean_array_size(v_args_2150_);
v___x_2154_ = ((size_t)0ULL);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_2153_, v___x_2154_, v_args_2150_);
v___x_2156_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2157_ = lean_box(2);
v___x_2158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v___x_2156_);
lean_ctor_set(v___x_2158_, 2, v___x_2155_);
v___x_2159_ = l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(v_bs_2149_);
v___x_2160_ = l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter(v_c_2148_);
lean_dec(v_c_2148_);
v___x_2161_ = lean_mk_empty_array_with_capacity(v___x_2147_);
v___x_2162_ = lean_array_push(v___x_2161_, v___x_2152_);
v___x_2163_ = lean_array_push(v___x_2162_, v___x_2142_);
v___x_2164_ = lean_array_push(v___x_2163_, v___x_2158_);
v___x_2165_ = lean_array_push(v___x_2164_, v___x_2159_);
v___x_2166_ = lean_array_push(v___x_2165_, v___x_2160_);
v___x_2167_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2151_, v___x_2166_);
return v___x_2167_;
}
}
else
{
lean_object* v___x_2168_; lean_object* v_o_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2168_ = lean_unsigned_to_nat(0u);
v_o_2169_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2168_);
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2170_);
lean_inc(v___x_2171_);
v___x_2172_ = l_Lean_Syntax_matchesNull(v___x_2171_, v___x_2168_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2171_);
v___x_2174_ = l_Lean_Syntax_matchesNull(v___x_2171_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec(v___x_2171_);
lean_dec(v_o_2169_);
return v_stx_1993_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v_s_2178_; lean_object* v___x_2179_; lean_object* v_c_2180_; lean_object* v_args_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; size_t v_sz_2184_; size_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2175_ = l_Lean_Syntax_getArg(v___x_2171_, v___x_2168_);
v___x_2176_ = l_Lean_Syntax_getArg(v___x_2171_, v___x_2170_);
lean_dec(v___x_2171_);
v___x_2177_ = lean_unsigned_to_nat(3u);
v_s_2178_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2177_);
v___x_2179_ = lean_unsigned_to_nat(4u);
v_c_2180_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2179_);
lean_dec(v_stx_1993_);
v_args_2181_ = l_Lean_Syntax_getArgs(v___x_2176_);
lean_dec(v___x_2176_);
v___x_2182_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__36));
v___x_2183_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_o_2169_);
lean_dec(v_o_2169_);
v_sz_2184_ = lean_array_size(v_args_2181_);
v___x_2185_ = ((size_t)0ULL);
v___x_2186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_inlineToParser_spec__0(v_sz_2184_, v___x_2185_, v_args_2181_);
v___x_2187_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2188_ = lean_box(2);
v___x_2189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v___x_2187_);
lean_ctor_set(v___x_2189_, 2, v___x_2186_);
v___x_2190_ = lean_mk_empty_array_with_capacity(v___x_2173_);
v___x_2191_ = lean_array_push(v___x_2190_, v___x_2175_);
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2189_);
v___x_2193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2188_);
lean_ctor_set(v___x_2193_, 1, v___x_2187_);
lean_ctor_set(v___x_2193_, 2, v___x_2192_);
v___x_2194_ = l_Lean_TSyntax_getString(v_s_2178_);
v___x_2195_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_s_2178_, v___x_2194_, v___x_2172_);
lean_dec(v_s_2178_);
v___x_2196_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_c_2180_);
lean_dec(v_c_2180_);
v___x_2197_ = lean_mk_empty_array_with_capacity(v___x_2179_);
v___x_2198_ = lean_array_push(v___x_2197_, v___x_2183_);
v___x_2199_ = lean_array_push(v___x_2198_, v___x_2193_);
v___x_2200_ = lean_array_push(v___x_2199_, v___x_2195_);
v___x_2201_ = lean_array_push(v___x_2200_, v___x_2196_);
v___x_2202_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2182_, v___x_2201_);
return v___x_2202_;
}
}
else
{
lean_object* v___x_2203_; lean_object* v_s_2204_; lean_object* v___x_2205_; lean_object* v_c_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec(v___x_2171_);
v___x_2203_ = lean_unsigned_to_nat(3u);
v_s_2204_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2203_);
v___x_2205_ = lean_unsigned_to_nat(4u);
v_c_2206_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2205_);
lean_dec(v_stx_1993_);
v___x_2207_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__36));
v___x_2208_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_o_2169_);
lean_dec(v_o_2169_);
v___x_2209_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__38));
v___x_2210_ = l_Lean_TSyntax_getString(v_s_2204_);
v___x_2211_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_s_2204_, v___x_2210_, v___x_2003_);
lean_dec(v_s_2204_);
v___x_2212_ = l___private_Lean_DocString_View_0__Lean_Doc_asFence(v_c_2206_);
lean_dec(v_c_2206_);
v___x_2213_ = lean_mk_empty_array_with_capacity(v___x_2205_);
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2208_);
v___x_2215_ = lean_array_push(v___x_2214_, v___x_2209_);
v___x_2216_ = lean_array_push(v___x_2215_, v___x_2211_);
v___x_2217_ = lean_array_push(v___x_2216_, v___x_2212_);
v___x_2218_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2207_, v___x_2217_);
return v___x_2218_;
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v_items_2221_; lean_object* v___x_2222_; size_t v_sz_2223_; size_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2219_);
lean_dec(v_stx_1993_);
v_items_2221_ = l_Lean_Syntax_getArgs(v___x_2220_);
lean_dec(v___x_2220_);
v___x_2222_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__39));
v_sz_2223_ = lean_array_size(v_items_2221_);
v___x_2224_ = ((size_t)0ULL);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(v_sz_2223_, v___x_2224_, v_items_2221_);
v___x_2226_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2227_ = lean_box(2);
v___x_2228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2226_);
lean_ctor_set(v___x_2228_, 2, v___x_2225_);
v___x_2229_ = lean_mk_empty_array_with_capacity(v___x_2219_);
v___x_2230_ = lean_array_push(v___x_2229_, v___x_2228_);
v___x_2231_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2222_, v___x_2230_);
return v___x_2231_;
}
}
else
{
lean_object* v___x_2232_; lean_object* v_n_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v_items_2236_; size_t v_sz_2237_; size_t v___x_2238_; lean_object* v_numbered_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2232_ = lean_unsigned_to_nat(1u);
v_n_2233_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2232_);
v___x_2234_ = lean_unsigned_to_nat(4u);
v___x_2235_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2234_);
lean_dec(v_stx_1993_);
v_items_2236_ = l_Lean_Syntax_getArgs(v___x_2235_);
lean_dec(v___x_2235_);
v_sz_2237_ = lean_array_size(v_items_2236_);
v___x_2238_ = ((size_t)0ULL);
v_numbered_2239_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(v_n_2233_, v_sz_2237_, v___x_2238_, v_items_2236_);
lean_dec(v_n_2233_);
v___x_2240_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__40));
v___x_2241_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2242_ = lean_box(2);
v___x_2243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
lean_ctor_set(v___x_2243_, 1, v___x_2241_);
lean_ctor_set(v___x_2243_, 2, v_numbered_2239_);
v___x_2244_ = lean_mk_empty_array_with_capacity(v___x_2232_);
v___x_2245_ = lean_array_push(v___x_2244_, v___x_2243_);
v___x_2246_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2240_, v___x_2245_);
return v___x_2246_;
}
}
else
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_items_2249_; lean_object* v___x_2250_; size_t v_sz_2251_; size_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2247_ = lean_unsigned_to_nat(1u);
v___x_2248_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2247_);
lean_dec(v_stx_1993_);
v_items_2249_ = l_Lean_Syntax_getArgs(v___x_2248_);
lean_dec(v___x_2248_);
v___x_2250_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__41));
v_sz_2251_ = lean_array_size(v_items_2249_);
v___x_2252_ = ((size_t)0ULL);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(v_sz_2251_, v___x_2252_, v_items_2249_);
v___x_2254_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2255_ = lean_box(2);
v___x_2256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
lean_ctor_set(v___x_2256_, 1, v___x_2254_);
lean_ctor_set(v___x_2256_, 2, v___x_2253_);
v___x_2257_ = lean_mk_empty_array_with_capacity(v___x_2247_);
v___x_2258_ = lean_array_push(v___x_2257_, v___x_2256_);
v___x_2259_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2250_, v___x_2258_);
return v___x_2259_;
}
}
else
{
lean_object* v___x_2260_; lean_object* v_gt_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_bs_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2260_ = lean_unsigned_to_nat(0u);
v_gt_2261_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2260_);
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2262_);
lean_dec(v_stx_1993_);
v_bs_2264_ = l_Lean_Syntax_getArgs(v___x_2263_);
lean_dec(v___x_2263_);
v___x_2265_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__42));
v___x_2266_ = l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(v_bs_2264_);
v___x_2267_ = lean_unsigned_to_nat(2u);
v___x_2268_ = lean_mk_empty_array_with_capacity(v___x_2267_);
v___x_2269_ = lean_array_push(v___x_2268_, v_gt_2261_);
v___x_2270_ = lean_array_push(v___x_2269_, v___x_2266_);
v___x_2271_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2265_, v___x_2270_);
return v___x_2271_;
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v_inls_2274_; lean_object* v___x_2275_; size_t v_sz_2276_; size_t v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = l_Lean_Syntax_getArg(v_stx_1993_, v___x_2272_);
lean_dec(v_stx_1993_);
v_inls_2274_ = l_Lean_Syntax_getArgs(v___x_2273_);
lean_dec(v___x_2273_);
v___x_2275_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__43));
v_sz_2276_ = lean_array_size(v_inls_2274_);
v___x_2277_ = ((size_t)0ULL);
v___x_2278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_inlineToParser_inlines_spec__2(v_sz_2276_, v___x_2277_, v_inls_2274_);
v___x_2279_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2280_ = lean_box(2);
v___x_2281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
lean_ctor_set(v___x_2281_, 1, v___x_2279_);
lean_ctor_set(v___x_2281_, 2, v___x_2278_);
v___x_2282_ = lean_mk_empty_array_with_capacity(v___x_2272_);
v___x_2283_ = lean_array_push(v___x_2282_, v___x_2281_);
v___x_2284_ = l___private_Lean_DocString_View_0__Lean_Doc_asNode(v___x_2275_, v___x_2283_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(size_t v_sz_2285_, size_t v_i_2286_, lean_object* v_bs_2287_){
_start:
{
uint8_t v___x_2288_; 
v___x_2288_ = lean_usize_dec_lt(v_i_2286_, v_sz_2285_);
if (v___x_2288_ == 0)
{
return v_bs_2287_;
}
else
{
lean_object* v_v_2289_; lean_object* v___x_2290_; lean_object* v_bs_x27_2291_; lean_object* v___x_2292_; size_t v___x_2293_; size_t v___x_2294_; lean_object* v___x_2295_; 
v_v_2289_ = lean_array_uget(v_bs_2287_, v_i_2286_);
v___x_2290_ = lean_unsigned_to_nat(0u);
v_bs_x27_2291_ = lean_array_uset(v_bs_2287_, v_i_2286_, v___x_2290_);
v___x_2292_ = l_Lean_Doc_blockToParser(v_v_2289_);
v___x_2293_ = ((size_t)1ULL);
v___x_2294_ = lean_usize_add(v_i_2286_, v___x_2293_);
v___x_2295_ = lean_array_uset(v_bs_x27_2291_, v_i_2286_, v___x_2292_);
v_i_2286_ = v___x_2294_;
v_bs_2287_ = v___x_2295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks(lean_object* v_bs_2297_){
_start:
{
size_t v_sz_2298_; size_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v_sz_2298_ = lean_array_size(v_bs_2297_);
v___x_2299_ = ((size_t)0ULL);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_2298_, v___x_2299_, v_bs_2297_);
v___x_2301_ = ((lean_object*)(l_Lean_Doc_mkVersoCodeBlockFrom___closed__1));
v___x_2302_ = lean_box(2);
v___x_2303_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v___x_2301_);
lean_ctor_set(v___x_2303_, 2, v___x_2300_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3___boxed(lean_object* v_sz_2304_, lean_object* v_i_2305_, lean_object* v_bs_2306_){
_start:
{
size_t v_sz_boxed_2307_; size_t v_i_boxed_2308_; lean_object* v_res_2309_; 
v_sz_boxed_2307_ = lean_unbox_usize(v_sz_2304_);
lean_dec(v_sz_2304_);
v_i_boxed_2308_ = lean_unbox_usize(v_i_2305_);
lean_dec(v_i_2305_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__3(v_sz_boxed_2307_, v_i_boxed_2308_, v_bs_2306_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0___boxed(lean_object* v_sz_2310_, lean_object* v_i_2311_, lean_object* v_bs_2312_){
_start:
{
size_t v_sz_boxed_2313_; size_t v_i_boxed_2314_; lean_object* v_res_2315_; 
v_sz_boxed_2313_ = lean_unbox_usize(v_sz_2310_);
lean_dec(v_sz_2310_);
v_i_boxed_2314_ = lean_unbox_usize(v_i_2311_);
lean_dec(v_i_2311_);
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_DocString_View_0__Lean_Doc_blockToParser_blocks_spec__0(v_sz_boxed_2313_, v_i_boxed_2314_, v_bs_2312_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5___boxed(lean_object* v_sz_2316_, lean_object* v_i_2317_, lean_object* v_bs_2318_){
_start:
{
size_t v_sz_boxed_2319_; size_t v_i_boxed_2320_; lean_object* v_res_2321_; 
v_sz_boxed_2319_ = lean_unbox_usize(v_sz_2316_);
lean_dec(v_sz_2316_);
v_i_boxed_2320_ = lean_unbox_usize(v_i_2317_);
lean_dec(v_i_2317_);
v_res_2321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_blockToParser_spec__5(v_sz_boxed_2319_, v_i_boxed_2320_, v_bs_2318_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg___boxed(lean_object* v_n_2322_, lean_object* v_sz_2323_, lean_object* v_i_2324_, lean_object* v_bs_2325_){
_start:
{
size_t v_sz_boxed_2326_; size_t v_i_boxed_2327_; lean_object* v_res_2328_; 
v_sz_boxed_2326_ = lean_unbox_usize(v_sz_2323_);
lean_dec(v_sz_2323_);
v_i_boxed_2327_ = lean_unbox_usize(v_i_2324_);
lean_dec(v_i_2324_);
v_res_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(v_n_2322_, v_sz_boxed_2326_, v_i_boxed_2327_, v_bs_2325_);
lean_dec(v_n_2322_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4(lean_object* v_n_2329_, lean_object* v_as_2330_, size_t v_sz_2331_, size_t v_i_2332_, lean_object* v_bs_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___redArg(v_n_2329_, v_sz_2331_, v_i_2332_, v_bs_2333_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4___boxed(lean_object* v_n_2335_, lean_object* v_as_2336_, lean_object* v_sz_2337_, lean_object* v_i_2338_, lean_object* v_bs_2339_){
_start:
{
size_t v_sz_boxed_2340_; size_t v_i_boxed_2341_; lean_object* v_res_2342_; 
v_sz_boxed_2340_ = lean_unbox_usize(v_sz_2337_);
lean_dec(v_sz_2337_);
v_i_boxed_2341_ = lean_unbox_usize(v_i_2338_);
lean_dec(v_i_2338_);
v_res_2342_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Doc_blockToParser_spec__4(v_n_2335_, v_as_2336_, v_sz_boxed_2340_, v_i_boxed_2341_, v_bs_2339_);
lean_dec_ref(v_as_2336_);
lean_dec(v_n_2335_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr1NilMkStr5__lean___lam__0(lean_object* v_s_2351_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__41));
v___x_2353_ = l_Lean_Doc_listItemToParser(v___x_2352_, v_s_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(lean_object* v_x_2360_){
_start:
{
lean_inc(v_x_2360_);
return v_x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0___boxed(lean_object* v_x_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__0(v_x_2361_);
lean_dec(v_x_2361_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1(lean_object* v___f_2382_, lean_object* v___f_2383_, lean_object* v_xs_2384_){
_start:
{
lean_object* v___x_2385_; size_t v_sz_2386_; size_t v___x_2387_; lean_object* v___x_2388_; size_t v_sz_2389_; lean_object* v___x_2390_; 
v___x_2385_ = ((lean_object*)(l_Lean_Doc_instCoeTSyntaxArrayConsSyntaxNodeKindMkStr1NilMkStr4__lean___lam__1___closed__9));
v_sz_2386_ = lean_array_size(v_xs_2384_);
v___x_2387_ = ((size_t)0ULL);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2385_, v___f_2382_, v_sz_2386_, v___x_2387_, v_xs_2384_);
v_sz_2389_ = lean_array_size(v___x_2388_);
v___x_2390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_2385_, v___f_2383_, v_sz_2389_, v___x_2387_, v___x_2388_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(size_t v_sz_2404_, size_t v_i_2405_, lean_object* v_bs_2406_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_usize_dec_lt(v_i_2405_, v_sz_2404_);
if (v___x_2407_ == 0)
{
return v_bs_2406_;
}
else
{
lean_object* v_v_2408_; lean_object* v___x_2409_; lean_object* v_bs_x27_2410_; lean_object* v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; lean_object* v___x_2414_; 
v_v_2408_ = lean_array_uget(v_bs_2406_, v_i_2405_);
v___x_2409_ = lean_unsigned_to_nat(0u);
v_bs_x27_2410_ = lean_array_uset(v_bs_2406_, v_i_2405_, v___x_2409_);
v___x_2411_ = l_Lean_Doc_inlineToParser(v_v_2408_);
v___x_2412_ = ((size_t)1ULL);
v___x_2413_ = lean_usize_add(v_i_2405_, v___x_2412_);
v___x_2414_ = lean_array_uset(v_bs_x27_2410_, v_i_2405_, v___x_2411_);
v_i_2405_ = v___x_2413_;
v_bs_2406_ = v___x_2414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0___boxed(lean_object* v_sz_2416_, lean_object* v_i_2417_, lean_object* v_bs_2418_){
_start:
{
size_t v_sz_boxed_2419_; size_t v_i_boxed_2420_; lean_object* v_res_2421_; 
v_sz_boxed_2419_ = lean_unbox_usize(v_sz_2416_);
lean_dec(v_sz_2416_);
v_i_boxed_2420_ = lean_unbox_usize(v_i_2417_);
lean_dec(v_i_2417_);
v_res_2421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(v_sz_boxed_2419_, v_i_boxed_2420_, v_bs_2418_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(size_t v_sz_2422_, size_t v_i_2423_, lean_object* v_bs_2424_){
_start:
{
uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_lt(v_i_2423_, v_sz_2422_);
if (v___x_2425_ == 0)
{
return v_bs_2424_;
}
else
{
lean_object* v_v_2426_; lean_object* v___x_2427_; lean_object* v_bs_x27_2428_; size_t v___x_2429_; size_t v___x_2430_; lean_object* v___x_2431_; 
v_v_2426_ = lean_array_uget(v_bs_2424_, v_i_2423_);
v___x_2427_ = lean_unsigned_to_nat(0u);
v_bs_x27_2428_ = lean_array_uset(v_bs_2424_, v_i_2423_, v___x_2427_);
v___x_2429_ = ((size_t)1ULL);
v___x_2430_ = lean_usize_add(v_i_2423_, v___x_2429_);
v___x_2431_ = lean_array_uset(v_bs_x27_2428_, v_i_2423_, v_v_2426_);
v_i_2423_ = v___x_2430_;
v_bs_2424_ = v___x_2431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1___boxed(lean_object* v_sz_2433_, lean_object* v_i_2434_, lean_object* v_bs_2435_){
_start:
{
size_t v_sz_boxed_2436_; size_t v_i_boxed_2437_; lean_object* v_res_2438_; 
v_sz_boxed_2436_ = lean_unbox_usize(v_sz_2433_);
lean_dec(v_sz_2433_);
v_i_boxed_2437_ = lean_unbox_usize(v_i_2434_);
lean_dec(v_i_2434_);
v_res_2438_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(v_sz_boxed_2436_, v_i_boxed_2437_, v_bs_2435_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateInlines(lean_object* v_xs_2439_){
_start:
{
size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_2442_; size_t v_sz_2443_; lean_object* v___x_2444_; 
v_sz_2440_ = lean_array_size(v_xs_2439_);
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__0(v_sz_2440_, v___x_2441_, v_xs_2439_);
v_sz_2443_ = lean_array_size(v___x_2442_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(v_sz_2443_, v___x_2441_, v___x_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(size_t v_sz_2445_, size_t v_i_2446_, lean_object* v_bs_2447_){
_start:
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_usize_dec_lt(v_i_2446_, v_sz_2445_);
if (v___x_2448_ == 0)
{
return v_bs_2447_;
}
else
{
lean_object* v_v_2449_; lean_object* v___x_2450_; lean_object* v_bs_x27_2451_; lean_object* v___x_2452_; size_t v___x_2453_; size_t v___x_2454_; lean_object* v___x_2455_; 
v_v_2449_ = lean_array_uget(v_bs_2447_, v_i_2446_);
v___x_2450_ = lean_unsigned_to_nat(0u);
v_bs_x27_2451_ = lean_array_uset(v_bs_2447_, v_i_2446_, v___x_2450_);
v___x_2452_ = l_Lean_Doc_blockToParser(v_v_2449_);
v___x_2453_ = ((size_t)1ULL);
v___x_2454_ = lean_usize_add(v_i_2446_, v___x_2453_);
v___x_2455_ = lean_array_uset(v_bs_x27_2451_, v_i_2446_, v___x_2452_);
v_i_2446_ = v___x_2454_;
v_bs_2447_ = v___x_2455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0___boxed(lean_object* v_sz_2457_, lean_object* v_i_2458_, lean_object* v_bs_2459_){
_start:
{
size_t v_sz_boxed_2460_; size_t v_i_boxed_2461_; lean_object* v_res_2462_; 
v_sz_boxed_2460_ = lean_unbox_usize(v_sz_2457_);
lean_dec(v_sz_2457_);
v_i_boxed_2461_ = lean_unbox_usize(v_i_2458_);
lean_dec(v_i_2458_);
v_res_2462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(v_sz_boxed_2460_, v_i_boxed_2461_, v_bs_2459_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_migrateBlocks(lean_object* v_xs_2463_){
_start:
{
size_t v_sz_2464_; size_t v___x_2465_; lean_object* v___x_2466_; size_t v_sz_2467_; lean_object* v___x_2468_; 
v_sz_2464_ = lean_array_size(v_xs_2463_);
v___x_2465_ = ((size_t)0ULL);
v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateBlocks_spec__0(v_sz_2464_, v___x_2465_, v_xs_2463_);
v_sz_2467_ = lean_array_size(v___x_2466_);
v___x_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_migrateInlines_spec__1(v_sz_2467_, v___x_2465_, v___x_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit(lean_object* v_s_2469_){
_start:
{
lean_object* v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = l_Lean_TSyntax_getString(v_s_2469_);
v___x_2471_ = 0;
v___x_2472_ = l_Lean_Doc_mkVersoCodeFrom(v_s_2469_, v___x_2470_, v___x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeOfStrLit___boxed(lean_object* v_s_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Doc_versoCodeOfStrLit(v_s_2473_);
lean_dec(v_s_2473_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit(lean_object* v_s_2475_){
_start:
{
lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = l_Lean_TSyntax_getString(v_s_2475_);
v___x_2477_ = 0;
v___x_2478_ = l_Lean_Doc_mkVersoCodeBlockFrom(v_s_2475_, v___x_2476_, v___x_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBlockOfStrLit___boxed(lean_object* v_s_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_Doc_versoCodeBlockOfStrLit(v_s_2479_);
lean_dec(v_s_2479_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkTargetView_of(lean_object* v_stx_2493_){
_start:
{
lean_object* v___x_2494_; uint8_t v___x_2495_; 
v___x_2494_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__6));
lean_inc(v_stx_2493_);
v___x_2495_ = l_Lean_Syntax_isOfKind(v_stx_2493_, v___x_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2496_ = ((lean_object*)(l_Lean_Doc_linkTargetToParser___closed__5));
lean_inc(v_stx_2493_);
v___x_2497_ = l_Lean_Syntax_isOfKind(v_stx_2493_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_dec(v_stx_2493_);
v___x_2498_ = lean_box(0);
return v___x_2498_;
}
else
{
lean_object* v___x_2499_; lean_object* v_o_2500_; lean_object* v___x_2501_; lean_object* v_name_2502_; 
v___x_2499_ = lean_unsigned_to_nat(0u);
v_o_2500_ = l_Lean_Syntax_getArg(v_stx_2493_, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(1u);
v_name_2502_ = l_Lean_Syntax_getArg(v_stx_2493_, v___x_2501_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2508_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_2502_);
v___x_2509_ = l_Lean_Syntax_isOfKind(v_name_2502_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
lean_dec(v_name_2502_);
lean_dec(v_o_2500_);
lean_dec(v_stx_2493_);
v___x_2510_ = lean_box(0);
return v___x_2510_;
}
else
{
goto v___jp_2503_;
}
}
else
{
goto v___jp_2503_;
}
v___jp_2503_:
{
lean_object* v___x_2504_; lean_object* v_c_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2504_ = lean_unsigned_to_nat(2u);
v_c_2505_ = l_Lean_Syntax_getArg(v_stx_2493_, v___x_2504_);
v___x_2506_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2506_, 0, v_stx_2493_);
lean_ctor_set(v___x_2506_, 1, v_o_2500_);
lean_ctor_set(v___x_2506_, 2, v_name_2502_);
lean_ctor_set(v___x_2506_, 3, v_c_2505_);
v___x_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
}
else
{
lean_object* v___x_2511_; lean_object* v_url_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2511_ = lean_unsigned_to_nat(1u);
v_url_2512_ = l_Lean_Syntax_getArg(v_stx_2493_, v___x_2511_);
v___x_2513_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__3));
lean_inc(v_url_2512_);
v___x_2514_ = l_Lean_Syntax_isOfKind(v_url_2512_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
lean_dec(v_url_2512_);
lean_dec(v_stx_2493_);
v___x_2515_ = lean_box(0);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; lean_object* v_o_2517_; lean_object* v___x_2518_; lean_object* v_c_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2516_ = lean_unsigned_to_nat(0u);
v_o_2517_ = l_Lean_Syntax_getArg(v_stx_2493_, v___x_2516_);
v___x_2518_ = lean_unsigned_to_nat(2u);
v_c_2519_ = l_Lean_Syntax_getArg(v_stx_2493_, v___x_2518_);
v___x_2520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2520_, 0, v_stx_2493_);
lean_ctor_set(v___x_2520_, 1, v_o_2517_);
lean_ctor_set(v___x_2520_, 2, v_url_2512_);
lean_ctor_set(v___x_2520_, 3, v_c_2519_);
v___x_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_narrowToValue_shrink(lean_object* v_a_2522_){
_start:
{
switch(lean_obj_tag(v_a_2522_))
{
case 0:
{
lean_object* v_leading_2523_; lean_object* v_trailing_2524_; lean_object* v_pos_2525_; lean_object* v_endPos_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2558_; 
v_leading_2523_ = lean_ctor_get(v_a_2522_, 0);
v_trailing_2524_ = lean_ctor_get(v_a_2522_, 2);
v_pos_2525_ = lean_ctor_get(v_a_2522_, 1);
v_endPos_2526_ = lean_ctor_get(v_a_2522_, 3);
v_isSharedCheck_2558_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2528_ = v_a_2522_;
v_isShared_2529_ = v_isSharedCheck_2558_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_endPos_2526_);
lean_inc(v_trailing_2524_);
lean_inc(v_pos_2525_);
lean_inc(v_leading_2523_);
lean_dec(v_a_2522_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2558_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_str_2530_; lean_object* v_startPos_2531_; lean_object* v_stopPos_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2557_; 
v_str_2530_ = lean_ctor_get(v_leading_2523_, 0);
v_startPos_2531_ = lean_ctor_get(v_leading_2523_, 1);
v_stopPos_2532_ = lean_ctor_get(v_leading_2523_, 2);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_leading_2523_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2534_ = v_leading_2523_;
v_isShared_2535_ = v_isSharedCheck_2557_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_stopPos_2532_);
lean_inc(v_startPos_2531_);
lean_inc(v_str_2530_);
lean_dec(v_leading_2523_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2557_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_str_2536_; lean_object* v_startPos_2537_; lean_object* v_stopPos_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2556_; 
v_str_2536_ = lean_ctor_get(v_trailing_2524_, 0);
v_startPos_2537_ = lean_ctor_get(v_trailing_2524_, 1);
v_stopPos_2538_ = lean_ctor_get(v_trailing_2524_, 2);
v_isSharedCheck_2556_ = !lean_is_exclusive(v_trailing_2524_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2540_ = v_trailing_2524_;
v_isShared_2541_ = v_isSharedCheck_2556_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_stopPos_2538_);
lean_inc(v_startPos_2537_);
lean_inc(v_str_2536_);
lean_dec(v_trailing_2524_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2556_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2542_ = lean_unsigned_to_nat(1u);
v___x_2543_ = lean_nat_add(v___x_2542_, v_stopPos_2532_);
lean_dec(v_stopPos_2532_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 2, v___x_2543_);
lean_ctor_set(v___x_2540_, 1, v_startPos_2531_);
lean_ctor_set(v___x_2540_, 0, v_str_2530_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_str_2530_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_startPos_2531_);
lean_ctor_set(v_reuseFailAlloc_2555_, 2, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2546_ = lean_nat_add(v___x_2542_, v_pos_2525_);
lean_dec(v_pos_2525_);
v___x_2547_ = lean_nat_sub(v_startPos_2537_, v___x_2542_);
lean_dec(v_startPos_2537_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 2, v_stopPos_2538_);
lean_ctor_set(v___x_2534_, 1, v___x_2547_);
lean_ctor_set(v___x_2534_, 0, v_str_2536_);
v___x_2549_ = v___x_2534_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_str_2536_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_stopPos_2538_);
v___x_2549_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2550_ = lean_nat_sub(v_endPos_2526_, v___x_2542_);
lean_dec(v_endPos_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 3, v___x_2550_);
lean_ctor_set(v___x_2528_, 2, v___x_2549_);
lean_ctor_set(v___x_2528_, 1, v___x_2546_);
lean_ctor_set(v___x_2528_, 0, v___x_2545_);
v___x_2552_ = v___x_2528_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
}
}
case 1:
{
lean_object* v_pos_2559_; lean_object* v_endPos_2560_; uint8_t v_canonical_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2571_; 
v_pos_2559_ = lean_ctor_get(v_a_2522_, 0);
v_endPos_2560_ = lean_ctor_get(v_a_2522_, 1);
v_canonical_2561_ = lean_ctor_get_uint8(v_a_2522_, sizeof(void*)*2);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2563_ = v_a_2522_;
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_endPos_2560_);
lean_inc(v_pos_2559_);
lean_dec(v_a_2522_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2571_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2569_; 
v___x_2565_ = lean_unsigned_to_nat(1u);
v___x_2566_ = lean_nat_add(v___x_2565_, v_pos_2559_);
lean_dec(v_pos_2559_);
v___x_2567_ = lean_nat_sub(v_endPos_2560_, v___x_2565_);
lean_dec(v_endPos_2560_);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 1, v___x_2567_);
lean_ctor_set(v___x_2563_, 0, v___x_2566_);
v___x_2569_ = v___x_2563_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v___x_2567_);
lean_ctor_set_uint8(v_reuseFailAlloc_2570_, sizeof(void*)*2, v_canonical_2561_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
default: 
{
return v_a_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_View_0__Lean_Doc_narrowToValue(lean_object* v_content_2572_){
_start:
{
lean_object* v___y_2574_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = l_Lean_Doc_versoCodeKind;
v___x_2611_ = l_Lean_Syntax_isLit_x3f(v___x_2610_, v_content_2572_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__2));
v___y_2574_ = v___x_2612_;
goto v___jp_2573_;
}
else
{
lean_object* v_val_2613_; 
v_val_2613_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_val_2613_);
lean_dec_ref_known(v___x_2611_, 1);
v___y_2574_ = v_val_2613_;
goto v___jp_2573_;
}
v___jp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2575_ = lean_string_length(v___y_2574_);
lean_dec_ref(v___y_2574_);
v___x_2576_ = l_Lean_TSyntax_getVersoCode(v_content_2572_);
v___x_2577_ = lean_string_length(v___x_2576_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = lean_nat_dec_eq(v___x_2575_, v___x_2577_);
if (v___x_2578_ == 0)
{
if (lean_obj_tag(v_content_2572_) == 1)
{
lean_object* v_info_2579_; lean_object* v_kind_2580_; lean_object* v_args_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_info_2579_ = lean_ctor_get(v_content_2572_, 0);
v_kind_2580_ = lean_ctor_get(v_content_2572_, 1);
v_args_2581_ = lean_ctor_get(v_content_2572_, 2);
v___x_2582_ = lean_array_get_size(v_args_2581_);
v___x_2583_ = lean_unsigned_to_nat(1u);
v___x_2584_ = lean_nat_dec_eq(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
return v_content_2572_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = lean_array_fget(v_args_2581_, v___x_2585_);
if (lean_obj_tag(v___x_2586_) == 2)
{
lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2606_; 
lean_inc(v_kind_2580_);
lean_inc(v_info_2579_);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_content_2572_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; lean_object* v_unused_2608_; lean_object* v_unused_2609_; 
v_unused_2607_ = lean_ctor_get(v_content_2572_, 2);
lean_dec(v_unused_2607_);
v_unused_2608_ = lean_ctor_get(v_content_2572_, 1);
lean_dec(v_unused_2608_);
v_unused_2609_ = lean_ctor_get(v_content_2572_, 0);
lean_dec(v_unused_2609_);
v___x_2588_ = v_content_2572_;
v_isShared_2589_ = v_isSharedCheck_2606_;
goto v_resetjp_2587_;
}
else
{
lean_dec(v_content_2572_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2606_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_info_2590_; lean_object* v_val_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2605_; 
v_info_2590_ = lean_ctor_get(v___x_2586_, 0);
v_val_2591_ = lean_ctor_get(v___x_2586_, 1);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2593_ = v___x_2586_;
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_val_2591_);
lean_inc(v_info_2590_);
lean_dec(v___x_2586_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2595_ = l___private_Lean_DocString_View_0__Lean_Doc_narrowToValue_shrink(v_info_2579_);
v___x_2596_ = l___private_Lean_DocString_View_0__Lean_Doc_narrowToValue_shrink(v_info_2590_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2596_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_val_2591_);
v___x_2598_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2599_ = lean_mk_empty_array_with_capacity(v___x_2583_);
v___x_2600_ = lean_array_push(v___x_2599_, v___x_2598_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 2, v___x_2600_);
lean_ctor_set(v___x_2588_, 0, v___x_2595_);
v___x_2602_ = v___x_2588_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_kind_2580_);
lean_ctor_set(v_reuseFailAlloc_2603_, 2, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
else
{
lean_dec(v___x_2586_);
return v_content_2572_;
}
}
}
else
{
return v_content_2572_;
}
}
else
{
return v_content_2572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText(lean_object* v_v_2614_){
_start:
{
lean_object* v_content_2615_; lean_object* v___x_2616_; 
v_content_2615_ = lean_ctor_get(v_v_2614_, 1);
v___x_2616_ = l_Lean_TSyntax_getVersoText(v_content_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoText___boxed(lean_object* v_v_2617_){
_start:
{
lean_object* v_res_2618_; 
v_res_2618_ = l_Lean_Doc_TextView_getVersoText(v_v_2617_);
lean_dec_ref(v_v_2617_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource(lean_object* v_v_2619_){
_start:
{
lean_object* v_content_2620_; lean_object* v___x_2621_; 
v_content_2620_ = lean_ctor_get(v_v_2619_, 1);
v___x_2621_ = l_Lean_TSyntax_getVersoTextSource(v_content_2620_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_getVersoTextSource___boxed(lean_object* v_v_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_Doc_TextView_getVersoTextSource(v_v_2622_);
lean_dec_ref(v_v_2622_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_TextView_of(lean_object* v_stx_2630_){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__46));
lean_inc(v_stx_2630_);
v___x_2632_ = l_Lean_Syntax_isOfKind(v_stx_2630_, v___x_2631_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec(v_stx_2630_);
v___x_2633_ = lean_box(0);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; lean_object* v_s_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2634_ = lean_unsigned_to_nat(0u);
v_s_2635_ = l_Lean_Syntax_getArg(v_stx_2630_, v___x_2634_);
v___x_2636_ = ((lean_object*)(l_Lean_Doc_TextView_of___closed__1));
lean_inc(v_s_2635_);
v___x_2637_ = l_Lean_Syntax_isOfKind(v_s_2635_, v___x_2636_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_dec(v_s_2635_);
lean_dec(v_stx_2630_);
v___x_2638_ = lean_box(0);
return v___x_2638_;
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_stx_2630_);
lean_ctor_set(v___x_2639_, 1, v_s_2635_);
v___x_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_EmphView_of(lean_object* v_stx_2641_){
_start:
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__42));
lean_inc(v_stx_2641_);
v___x_2643_ = l_Lean_Syntax_isOfKind(v_stx_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
lean_dec(v_stx_2641_);
v___x_2644_ = lean_box(0);
return v___x_2644_;
}
else
{
lean_object* v___x_2645_; lean_object* v_o_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2645_ = lean_unsigned_to_nat(0u);
v_o_2646_ = l_Lean_Syntax_getArg(v_stx_2641_, v___x_2645_);
v___x_2647_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__44));
lean_inc(v_o_2646_);
v___x_2648_ = l_Lean_Syntax_isOfKind(v_o_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
lean_dec(v_o_2646_);
lean_dec(v_stx_2641_);
v___x_2649_ = lean_box(0);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v_c_2651_; uint8_t v___x_2652_; 
v___x_2650_ = lean_unsigned_to_nat(2u);
v_c_2651_ = l_Lean_Syntax_getArg(v_stx_2641_, v___x_2650_);
lean_inc(v_c_2651_);
v___x_2652_ = l_Lean_Syntax_isOfKind(v_c_2651_, v___x_2647_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec(v_c_2651_);
lean_dec(v_o_2646_);
lean_dec(v_stx_2641_);
v___x_2653_ = lean_box(0);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_inl_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2654_ = lean_unsigned_to_nat(1u);
v___x_2655_ = l_Lean_Syntax_getArg(v_stx_2641_, v___x_2654_);
v_inl_2656_ = l_Lean_Syntax_getArgs(v___x_2655_);
lean_dec(v___x_2655_);
v___x_2657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2657_, 0, v_stx_2641_);
lean_ctor_set(v___x_2657_, 1, v_o_2646_);
lean_ctor_set(v___x_2657_, 2, v_inl_2656_);
lean_ctor_set(v___x_2657_, 3, v_c_2651_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BoldView_of(lean_object* v_stx_2659_){
_start:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__38));
lean_inc(v_stx_2659_);
v___x_2661_ = l_Lean_Syntax_isOfKind(v_stx_2659_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec(v_stx_2659_);
v___x_2662_ = lean_box(0);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v_o_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2663_ = lean_unsigned_to_nat(0u);
v_o_2664_ = l_Lean_Syntax_getArg(v_stx_2659_, v___x_2663_);
v___x_2665_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__40));
lean_inc(v_o_2664_);
v___x_2666_ = l_Lean_Syntax_isOfKind(v_o_2664_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec(v_o_2664_);
lean_dec(v_stx_2659_);
v___x_2667_ = lean_box(0);
return v___x_2667_;
}
else
{
lean_object* v___x_2668_; lean_object* v_c_2669_; uint8_t v___x_2670_; 
v___x_2668_ = lean_unsigned_to_nat(2u);
v_c_2669_ = l_Lean_Syntax_getArg(v_stx_2659_, v___x_2668_);
lean_inc(v_c_2669_);
v___x_2670_ = l_Lean_Syntax_isOfKind(v_c_2669_, v___x_2665_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec(v_c_2669_);
lean_dec(v_o_2664_);
lean_dec(v_stx_2659_);
v___x_2671_ = lean_box(0);
return v___x_2671_;
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v_inl_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = l_Lean_Syntax_getArg(v_stx_2659_, v___x_2672_);
v_inl_2674_ = l_Lean_Syntax_getArgs(v___x_2673_);
lean_dec(v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2675_, 0, v_stx_2659_);
lean_ctor_set(v___x_2675_, 1, v_o_2664_);
lean_ctor_set(v___x_2675_, 2, v_inl_2674_);
lean_ctor_set(v___x_2675_, 3, v_c_2669_);
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode(lean_object* v_v_2677_){
_start:
{
lean_object* v_content_2678_; lean_object* v___x_2679_; 
v_content_2678_ = lean_ctor_get(v_v_2677_, 2);
v___x_2679_ = l_Lean_TSyntax_getVersoCode(v_content_2678_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_getVersoCode___boxed(lean_object* v_v_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_Doc_CodeView_getVersoCode(v_v_2680_);
lean_dec_ref(v_v_2680_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeView_of(lean_object* v_stx_2688_){
_start:
{
lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
lean_inc(v_stx_2688_);
v___x_2690_ = l_Lean_Syntax_isOfKind(v_stx_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; 
lean_dec(v_stx_2688_);
v___x_2691_ = lean_box(0);
return v___x_2691_;
}
else
{
lean_object* v___x_2692_; lean_object* v_o_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2692_ = lean_unsigned_to_nat(0u);
v_o_2693_ = l_Lean_Syntax_getArg(v_stx_2688_, v___x_2692_);
v___x_2694_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asCodeDelimiter___closed__1));
lean_inc(v_o_2693_);
v___x_2695_ = l_Lean_Syntax_isOfKind(v_o_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; 
lean_dec(v_o_2693_);
lean_dec(v_stx_2688_);
v___x_2696_ = lean_box(0);
return v___x_2696_;
}
else
{
lean_object* v___x_2697_; lean_object* v_s_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2697_ = lean_unsigned_to_nat(1u);
v_s_2698_ = l_Lean_Syntax_getArg(v_stx_2688_, v___x_2697_);
v___x_2699_ = ((lean_object*)(l_Lean_Doc_CodeView_of___closed__1));
lean_inc(v_s_2698_);
v___x_2700_ = l_Lean_Syntax_isOfKind(v_s_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_dec(v_s_2698_);
lean_dec(v_o_2693_);
lean_dec(v_stx_2688_);
v___x_2701_ = lean_box(0);
return v___x_2701_;
}
else
{
lean_object* v___x_2702_; lean_object* v_c_2703_; uint8_t v___x_2704_; 
v___x_2702_ = lean_unsigned_to_nat(2u);
v_c_2703_ = l_Lean_Syntax_getArg(v_stx_2688_, v___x_2702_);
lean_inc(v_c_2703_);
v___x_2704_ = l_Lean_Syntax_isOfKind(v_c_2703_, v___x_2694_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
lean_dec(v_c_2703_);
lean_dec(v_s_2698_);
lean_dec(v_o_2693_);
lean_dec(v_stx_2688_);
v___x_2705_ = lean_box(0);
return v___x_2705_;
}
else
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = l___private_Lean_DocString_View_0__Lean_Doc_narrowToValue(v_s_2698_);
v___x_2707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2707_, 0, v_stx_2688_);
lean_ctor_set(v___x_2707_, 1, v_o_2693_);
lean_ctor_set(v___x_2707_, 2, v___x_2706_);
lean_ctor_set(v___x_2707_, 3, v_c_2703_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode(lean_object* v_v_2709_){
_start:
{
lean_object* v_code_2710_; lean_object* v___x_2711_; 
v_code_2710_ = lean_ctor_get(v_v_2709_, 2);
v___x_2711_ = l_Lean_Doc_CodeView_getVersoCode(v_code_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_getVersoCode___boxed(lean_object* v_v_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_Doc_MathView_getVersoCode(v_v_2712_);
lean_dec_ref(v_v_2712_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MathView_of(lean_object* v_stx_2714_){
_start:
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__34));
lean_inc(v_stx_2714_);
v___x_2716_ = l_Lean_Syntax_isOfKind(v_stx_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__30));
lean_inc(v_stx_2714_);
v___x_2718_ = l_Lean_Syntax_isOfKind(v_stx_2714_, v___x_2717_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; 
lean_dec(v_stx_2714_);
v___x_2719_ = lean_box(0);
return v___x_2719_;
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___y_2723_; 
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = l_Lean_Syntax_getArg(v_stx_2714_, v___x_2720_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__32));
lean_inc(v___x_2721_);
v___x_2743_ = l_Lean_Syntax_isOfKind(v___x_2721_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; 
lean_dec(v___x_2721_);
lean_dec(v_stx_2714_);
v___x_2744_ = lean_box(0);
return v___x_2744_;
}
else
{
goto v___jp_2736_;
}
}
else
{
goto v___jp_2736_;
}
v___jp_2722_:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_Doc_CodeView_of(v___y_2723_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v___x_2725_; 
lean_dec(v___x_2721_);
lean_dec(v_stx_2714_);
v___x_2725_ = lean_box(0);
return v___x_2725_;
}
else
{
lean_object* v_val_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2735_; 
v_val_2726_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2728_ = v___x_2724_;
v_isShared_2729_ = v_isSharedCheck_2735_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_val_2726_);
lean_dec(v___x_2724_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2735_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
uint8_t v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2730_ = 1;
v___x_2731_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2731_, 0, v_stx_2714_);
lean_ctor_set(v___x_2731_, 1, v___x_2721_);
lean_ctor_set(v___x_2731_, 2, v_val_2726_);
lean_ctor_set_uint8(v___x_2731_, sizeof(void*)*3, v___x_2730_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2731_);
v___x_2733_ = v___x_2728_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
v___jp_2736_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_unsigned_to_nat(1u);
v___x_2738_ = l_Lean_Syntax_getArg(v_stx_2714_, v___x_2737_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
lean_inc(v___x_2738_);
v___x_2740_ = l_Lean_Syntax_isOfKind(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_dec(v___x_2738_);
lean_dec(v___x_2721_);
lean_dec(v_stx_2714_);
v___x_2741_ = lean_box(0);
return v___x_2741_;
}
else
{
v___y_2723_ = v___x_2738_;
goto v___jp_2722_;
}
}
else
{
v___y_2723_ = v___x_2738_;
goto v___jp_2722_;
}
}
}
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = l_Lean_Syntax_getArg(v_stx_2714_, v___x_2745_);
v___x_2747_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__36));
lean_inc(v___x_2746_);
v___x_2748_ = l_Lean_Syntax_isOfKind(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; 
lean_dec(v___x_2746_);
lean_dec(v_stx_2714_);
v___x_2749_ = lean_box(0);
return v___x_2749_;
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2750_ = lean_unsigned_to_nat(1u);
v___x_2751_ = l_Lean_Syntax_getArg(v_stx_2714_, v___x_2750_);
v___x_2752_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_inlineToParser_code___closed__1));
lean_inc(v___x_2751_);
v___x_2753_ = l_Lean_Syntax_isOfKind(v___x_2751_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
lean_dec(v___x_2751_);
lean_dec(v___x_2746_);
lean_dec(v_stx_2714_);
v___x_2754_ = lean_box(0);
return v___x_2754_;
}
else
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_Doc_CodeView_of(v___x_2751_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v___x_2756_; 
lean_dec(v___x_2746_);
lean_dec(v_stx_2714_);
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
else
{
lean_object* v_val_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2766_; 
v_val_2757_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2759_ = v___x_2755_;
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_val_2757_);
lean_dec(v___x_2755_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2761_ = 0;
v___x_2762_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2762_, 0, v_stx_2714_);
lean_ctor_set(v___x_2762_, 1, v___x_2746_);
lean_ctor_set(v___x_2762_, 2, v_val_2757_);
lean_ctor_set_uint8(v___x_2762_, sizeof(void*)*3, v___x_2761_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2762_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkView_of(lean_object* v_stx_2767_){
_start:
{
lean_object* v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__29));
lean_inc(v_stx_2767_);
v___x_2769_ = l_Lean_Syntax_isOfKind(v_stx_2767_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_dec(v_stx_2767_);
v___x_2770_ = lean_box(0);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v_tgt_2772_; lean_object* v___x_2773_; 
v___x_2771_ = lean_unsigned_to_nat(3u);
v_tgt_2772_ = l_Lean_Syntax_getArg(v_stx_2767_, v___x_2771_);
v___x_2773_ = l_Lean_Doc_LinkTargetView_of(v_tgt_2772_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v___x_2774_; 
lean_dec(v_stx_2767_);
v___x_2774_ = lean_box(0);
return v___x_2774_;
}
else
{
lean_object* v_val_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2790_; 
v_val_2775_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2777_ = v___x_2773_;
v_isShared_2778_ = v_isSharedCheck_2790_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_val_2775_);
lean_dec(v___x_2773_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2790_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v_o_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v_c_2784_; lean_object* v_inl_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2779_ = lean_unsigned_to_nat(0u);
v_o_2780_ = l_Lean_Syntax_getArg(v_stx_2767_, v___x_2779_);
v___x_2781_ = lean_unsigned_to_nat(1u);
v___x_2782_ = l_Lean_Syntax_getArg(v_stx_2767_, v___x_2781_);
v___x_2783_ = lean_unsigned_to_nat(2u);
v_c_2784_ = l_Lean_Syntax_getArg(v_stx_2767_, v___x_2783_);
v_inl_2785_ = l_Lean_Syntax_getArgs(v___x_2782_);
lean_dec(v___x_2782_);
v___x_2786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2786_, 0, v_stx_2767_);
lean_ctor_set(v___x_2786_, 1, v_o_2780_);
lean_ctor_set(v___x_2786_, 2, v_inl_2785_);
lean_ctor_set(v___x_2786_, 3, v_c_2784_);
lean_ctor_set(v___x_2786_, 4, v_val_2775_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2786_);
v___x_2788_ = v___x_2777_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt(lean_object* v_v_2791_){
_start:
{
lean_object* v_alt_2792_; lean_object* v___x_2793_; 
v_alt_2792_ = lean_ctor_get(v_v_2791_, 2);
v___x_2793_ = l_Lean_TSyntax_getVersoImageAlt(v_alt_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_getAlt___boxed(lean_object* v_v_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_Doc_ImageView_getAlt(v_v_2794_);
lean_dec_ref(v_v_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ImageView_of(lean_object* v_stx_2802_){
_start:
{
lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2803_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__27));
lean_inc(v_stx_2802_);
v___x_2804_ = l_Lean_Syntax_isOfKind(v_stx_2802_, v___x_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_dec(v_stx_2802_);
v___x_2805_ = lean_box(0);
return v___x_2805_;
}
else
{
lean_object* v___x_2806_; lean_object* v_alt_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2806_ = lean_unsigned_to_nat(1u);
v_alt_2807_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_2806_);
v___x_2808_ = ((lean_object*)(l_Lean_Doc_ImageView_of___closed__1));
lean_inc(v_alt_2807_);
v___x_2809_ = l_Lean_Syntax_isOfKind(v_alt_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec(v_alt_2807_);
lean_dec(v_stx_2802_);
v___x_2810_ = lean_box(0);
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v_tgt_2812_; lean_object* v___x_2813_; 
v___x_2811_ = lean_unsigned_to_nat(3u);
v_tgt_2812_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_2811_);
v___x_2813_ = l_Lean_Doc_LinkTargetView_of(v_tgt_2812_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v___x_2814_; 
lean_dec(v_alt_2807_);
lean_dec(v_stx_2802_);
v___x_2814_ = lean_box(0);
return v___x_2814_;
}
else
{
lean_object* v_val_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2827_; 
v_val_2815_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2817_ = v___x_2813_;
v_isShared_2818_ = v_isSharedCheck_2827_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_val_2815_);
lean_dec(v___x_2813_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2827_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v_o_2820_; lean_object* v___x_2821_; lean_object* v_c_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
v___x_2819_ = lean_unsigned_to_nat(0u);
v_o_2820_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_2819_);
v___x_2821_ = lean_unsigned_to_nat(2u);
v_c_2822_ = l_Lean_Syntax_getArg(v_stx_2802_, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2823_, 0, v_stx_2802_);
lean_ctor_set(v___x_2823_, 1, v_o_2820_);
lean_ctor_set(v___x_2823_, 2, v_alt_2807_);
lean_ctor_set(v___x_2823_, 3, v_c_2822_);
lean_ctor_set(v___x_2823_, 4, v_val_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2823_);
v___x_2825_ = v___x_2817_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName(lean_object* v_v_2828_){
_start:
{
lean_object* v_name_2829_; lean_object* v___x_2830_; 
v_name_2829_ = lean_ctor_get(v_v_2828_, 2);
v___x_2830_ = l_Lean_TSyntax_getVersoRefName(v_name_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_getName___boxed(lean_object* v_v_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Doc_FootnoteView_getName(v_v_2831_);
lean_dec_ref(v_v_2831_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteView_of(lean_object* v_stx_2833_){
_start:
{
lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2834_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__25));
lean_inc(v_stx_2833_);
v___x_2835_ = l_Lean_Syntax_isOfKind(v_stx_2833_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; 
lean_dec(v_stx_2833_);
v___x_2836_ = lean_box(0);
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; lean_object* v_name_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2837_ = lean_unsigned_to_nat(1u);
v_name_2838_ = l_Lean_Syntax_getArg(v_stx_2833_, v___x_2837_);
v___x_2839_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_2838_);
v___x_2840_ = l_Lean_Syntax_isOfKind(v_name_2838_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; 
lean_dec(v_name_2838_);
lean_dec(v_stx_2833_);
v___x_2841_ = lean_box(0);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v_o_2843_; lean_object* v___x_2844_; lean_object* v_c_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2842_ = lean_unsigned_to_nat(0u);
v_o_2843_ = l_Lean_Syntax_getArg(v_stx_2833_, v___x_2842_);
v___x_2844_ = lean_unsigned_to_nat(2u);
v_c_2845_ = l_Lean_Syntax_getArg(v_stx_2833_, v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2846_, 0, v_stx_2833_);
lean_ctor_set(v___x_2846_, 1, v_o_2843_);
lean_ctor_set(v___x_2846_, 2, v_name_2838_);
lean_ctor_set(v___x_2846_, 3, v_c_2845_);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinebreakView_of(lean_object* v_stx_2848_){
_start:
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = ((lean_object*)(l_Lean_Doc_mkVersoLinebreakFrom___closed__2));
lean_inc(v_stx_2848_);
v___x_2850_ = l_Lean_Syntax_isOfKind(v_stx_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec(v_stx_2848_);
v___x_2851_ = lean_box(0);
return v___x_2851_;
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2852_ = lean_unsigned_to_nat(0u);
v___x_2853_ = l_Lean_Syntax_getArg(v_stx_2848_, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v_stx_2848_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_RoleView_of(lean_object* v_stx_2856_){
_start:
{
lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = ((lean_object*)(l_Lean_Doc_inlineToParser___closed__20));
lean_inc(v_stx_2856_);
v___x_2858_ = l_Lean_Syntax_isOfKind(v_stx_2856_, v___x_2857_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_dec(v_stx_2856_);
v___x_2859_ = lean_box(0);
return v___x_2859_;
}
else
{
lean_object* v___x_2860_; lean_object* v_name_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2860_ = lean_unsigned_to_nat(1u);
v_name_2861_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2860_);
v___x_2862_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_2861_);
v___x_2863_ = l_Lean_Syntax_isOfKind(v_name_2861_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec(v_name_2861_);
lean_dec(v_stx_2856_);
v___x_2864_ = lean_box(0);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v_bo_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v_bc_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2865_ = lean_unsigned_to_nat(0u);
v_bo_2866_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2865_);
v___x_2867_ = lean_unsigned_to_nat(2u);
v___x_2868_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2867_);
v___x_2869_ = lean_unsigned_to_nat(3u);
v_bc_2870_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2869_);
v___x_2871_ = lean_unsigned_to_nat(4u);
v___x_2872_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2871_);
lean_inc(v___x_2872_);
v___x_2873_ = l_Lean_Syntax_matchesNull(v___x_2872_, v___x_2860_);
if (v___x_2873_ == 0)
{
uint8_t v___x_2874_; 
v___x_2874_ = l_Lean_Syntax_matchesNull(v___x_2872_, v___x_2865_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_dec(v_bc_2870_);
lean_dec(v___x_2868_);
lean_dec(v_bo_2866_);
lean_dec(v_name_2861_);
lean_dec(v_stx_2856_);
v___x_2875_ = lean_box(0);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2876_ = lean_unsigned_to_nat(6u);
v___x_2877_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2876_);
v___x_2878_ = l_Lean_Syntax_matchesNull(v___x_2877_, v___x_2865_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_bc_2870_);
lean_dec(v___x_2868_);
lean_dec(v_bo_2866_);
lean_dec(v_name_2861_);
lean_dec(v_stx_2856_);
v___x_2879_ = lean_box(0);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v_inl_2882_; lean_object* v_args_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2880_ = lean_unsigned_to_nat(5u);
v___x_2881_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2880_);
v_inl_2882_ = l_Lean_Syntax_getArgs(v___x_2881_);
lean_dec(v___x_2881_);
v_args_2883_ = l_Lean_Syntax_getArgs(v___x_2868_);
lean_dec(v___x_2868_);
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2885_, 0, v_stx_2856_);
lean_ctor_set(v___x_2885_, 1, v_bo_2866_);
lean_ctor_set(v___x_2885_, 2, v_name_2861_);
lean_ctor_set(v___x_2885_, 3, v_args_2883_);
lean_ctor_set(v___x_2885_, 4, v_bc_2870_);
lean_ctor_set(v___x_2885_, 5, v___x_2884_);
lean_ctor_set(v___x_2885_, 6, v_inl_2882_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = lean_unsigned_to_nat(6u);
v___x_2888_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2887_);
lean_inc(v___x_2888_);
v___x_2889_ = l_Lean_Syntax_matchesNull(v___x_2888_, v___x_2860_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
lean_dec(v___x_2888_);
lean_dec(v___x_2872_);
lean_dec(v_bc_2870_);
lean_dec(v___x_2868_);
lean_dec(v_bo_2866_);
lean_dec(v_name_2861_);
lean_dec(v_stx_2856_);
v___x_2890_ = lean_box(0);
return v___x_2890_;
}
else
{
lean_object* v_so_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v_sc_2894_; lean_object* v_inl_2895_; lean_object* v_args_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v_so_2891_ = l_Lean_Syntax_getArg(v___x_2872_, v___x_2865_);
lean_dec(v___x_2872_);
v___x_2892_ = lean_unsigned_to_nat(5u);
v___x_2893_ = l_Lean_Syntax_getArg(v_stx_2856_, v___x_2892_);
v_sc_2894_ = l_Lean_Syntax_getArg(v___x_2888_, v___x_2865_);
lean_dec(v___x_2888_);
v_inl_2895_ = l_Lean_Syntax_getArgs(v___x_2893_);
lean_dec(v___x_2893_);
v_args_2896_ = l_Lean_Syntax_getArgs(v___x_2868_);
lean_dec(v___x_2868_);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v_so_2891_);
lean_ctor_set(v___x_2897_, 1, v_sc_2894_);
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2899_, 0, v_stx_2856_);
lean_ctor_set(v___x_2899_, 1, v_bo_2866_);
lean_ctor_set(v___x_2899_, 2, v_name_2861_);
lean_ctor_set(v___x_2899_, 3, v_args_2896_);
lean_ctor_set(v___x_2899_, 4, v_bc_2870_);
lean_ctor_set(v___x_2899_, 5, v___x_2898_);
lean_ctor_set(v___x_2899_, 6, v_inl_2895_);
v___x_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
return v___x_2900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx(lean_object* v_x_2901_){
_start:
{
switch(lean_obj_tag(v_x_2901_))
{
case 0:
{
lean_object* v___x_2902_; 
v___x_2902_ = lean_unsigned_to_nat(0u);
return v___x_2902_;
}
case 1:
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_unsigned_to_nat(1u);
return v___x_2903_;
}
case 2:
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_unsigned_to_nat(2u);
return v___x_2904_;
}
case 3:
{
lean_object* v___x_2905_; 
v___x_2905_ = lean_unsigned_to_nat(3u);
return v___x_2905_;
}
case 4:
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_unsigned_to_nat(4u);
return v___x_2906_;
}
case 5:
{
lean_object* v___x_2907_; 
v___x_2907_ = lean_unsigned_to_nat(5u);
return v___x_2907_;
}
case 6:
{
lean_object* v___x_2908_; 
v___x_2908_ = lean_unsigned_to_nat(6u);
return v___x_2908_;
}
case 7:
{
lean_object* v___x_2909_; 
v___x_2909_ = lean_unsigned_to_nat(7u);
return v___x_2909_;
}
case 8:
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_unsigned_to_nat(8u);
return v___x_2910_;
}
default: 
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_unsigned_to_nat(9u);
return v___x_2911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorIdx___boxed(lean_object* v_x_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Doc_InlineView_ctorIdx(v_x_2912_);
lean_dec_ref(v_x_2912_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___redArg(lean_object* v_t_2914_, lean_object* v_k_2915_){
_start:
{
lean_object* v_view_2916_; lean_object* v___x_2917_; 
v_view_2916_ = lean_ctor_get(v_t_2914_, 0);
lean_inc_ref(v_view_2916_);
lean_dec_ref(v_t_2914_);
v___x_2917_ = lean_apply_1(v_k_2915_, v_view_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim(lean_object* v_motive_2918_, lean_object* v_ctorIdx_2919_, lean_object* v_t_2920_, lean_object* v_h_2921_, lean_object* v_k_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2920_, v_k_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_ctorElim___boxed(lean_object* v_motive_2924_, lean_object* v_ctorIdx_2925_, lean_object* v_t_2926_, lean_object* v_h_2927_, lean_object* v_k_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Doc_InlineView_ctorElim(v_motive_2924_, v_ctorIdx_2925_, v_t_2926_, v_h_2927_, v_k_2928_);
lean_dec(v_ctorIdx_2925_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim___redArg(lean_object* v_t_2930_, lean_object* v_text_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2930_, v_text_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_text_elim(lean_object* v_motive_2933_, lean_object* v_t_2934_, lean_object* v_h_2935_, lean_object* v_text_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2934_, v_text_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim___redArg(lean_object* v_t_2938_, lean_object* v_emph_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2938_, v_emph_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_emph_elim(lean_object* v_motive_2941_, lean_object* v_t_2942_, lean_object* v_h_2943_, lean_object* v_emph_2944_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2942_, v_emph_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim___redArg(lean_object* v_t_2946_, lean_object* v_bold_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2946_, v_bold_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_bold_elim(lean_object* v_motive_2949_, lean_object* v_t_2950_, lean_object* v_h_2951_, lean_object* v_bold_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2950_, v_bold_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim___redArg(lean_object* v_t_2954_, lean_object* v_code_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2954_, v_code_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_code_elim(lean_object* v_motive_2957_, lean_object* v_t_2958_, lean_object* v_h_2959_, lean_object* v_code_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2958_, v_code_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim___redArg(lean_object* v_t_2962_, lean_object* v_math_2963_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2962_, v_math_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_math_elim(lean_object* v_motive_2965_, lean_object* v_t_2966_, lean_object* v_h_2967_, lean_object* v_math_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2966_, v_math_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim___redArg(lean_object* v_t_2970_, lean_object* v_link_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2970_, v_link_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_link_elim(lean_object* v_motive_2973_, lean_object* v_t_2974_, lean_object* v_h_2975_, lean_object* v_link_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2974_, v_link_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim___redArg(lean_object* v_t_2978_, lean_object* v_image_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2978_, v_image_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_image_elim(lean_object* v_motive_2981_, lean_object* v_t_2982_, lean_object* v_h_2983_, lean_object* v_image_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2982_, v_image_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim___redArg(lean_object* v_t_2986_, lean_object* v_footnote_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2986_, v_footnote_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_footnote_elim(lean_object* v_motive_2989_, lean_object* v_t_2990_, lean_object* v_h_2991_, lean_object* v_footnote_2992_){
_start:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2990_, v_footnote_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim___redArg(lean_object* v_t_2994_, lean_object* v_linebreak_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2994_, v_linebreak_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_linebreak_elim(lean_object* v_motive_2997_, lean_object* v_t_2998_, lean_object* v_h_2999_, lean_object* v_linebreak_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_2998_, v_linebreak_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim___redArg(lean_object* v_t_3002_, lean_object* v_role_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_3002_, v_role_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_role_elim(lean_object* v_motive_3005_, lean_object* v_t_3006_, lean_object* v_h_3007_, lean_object* v_role_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_Doc_InlineView_ctorElim___redArg(v_t_3006_, v_role_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTextViewInlineView___lam__0(lean_object* v_view_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_view_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeEmphViewInlineView___lam__0(lean_object* v_view_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_view_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBoldViewInlineView___lam__0(lean_object* v_view_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3019_, 0, v_view_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeViewInlineView___lam__0(lean_object* v_view_3022_){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3023_, 0, v_view_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMathViewInlineView___lam__0(lean_object* v_view_3026_){
_start:
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_view_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkViewInlineView___lam__0(lean_object* v_view_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3031_, 0, v_view_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeImageViewInlineView___lam__0(lean_object* v_view_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3035_, 0, v_view_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteViewInlineView___lam__0(lean_object* v_view_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_view_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinebreakViewInlineView___lam__0(lean_object* v_view_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3043_, 0, v_view_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeRoleViewInlineView___lam__0(lean_object* v_view_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_view_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx(lean_object* v_x_3050_){
_start:
{
lean_object* v_view_3051_; lean_object* v_stx_3052_; 
v_view_3051_ = lean_ctor_get(v_x_3050_, 0);
v_stx_3052_ = lean_ctor_get(v_view_3051_, 0);
lean_inc(v_stx_3052_);
return v_stx_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_stx___boxed(lean_object* v_x_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Doc_InlineView_stx(v_x_3053_);
lean_dec_ref(v_x_3053_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_InlineView_of(lean_object* v_stx_3055_){
_start:
{
lean_object* v___x_3056_; 
lean_inc(v_stx_3055_);
v___x_3056_ = l_Lean_Doc_TextView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3057_; 
lean_inc(v_stx_3055_);
v___x_3057_ = l_Lean_Doc_EmphView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v___x_3058_; 
lean_inc(v_stx_3055_);
v___x_3058_ = l_Lean_Doc_BoldView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; 
lean_inc(v_stx_3055_);
v___x_3059_ = l_Lean_Doc_CodeView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v___x_3060_; 
lean_inc(v_stx_3055_);
v___x_3060_ = l_Lean_Doc_MathView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v___x_3061_; 
lean_inc(v_stx_3055_);
v___x_3061_ = l_Lean_Doc_LinkView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v___x_3062_; 
lean_inc(v_stx_3055_);
v___x_3062_ = l_Lean_Doc_ImageView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v___x_3063_; 
lean_inc(v_stx_3055_);
v___x_3063_ = l_Lean_Doc_FootnoteView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3064_; 
lean_inc(v_stx_3055_);
v___x_3064_ = l_Lean_Doc_LinebreakView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Doc_RoleView_of(v_stx_3055_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = lean_box(0);
return v___x_3066_;
}
else
{
lean_object* v_val_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3075_; 
v_val_3067_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3069_ = v___x_3065_;
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_val_3067_);
lean_dec(v___x_3065_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3071_, 0, v_val_3067_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_val_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
lean_dec(v_stx_3055_);
v_val_3076_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3078_ = v___x_3064_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_val_3076_);
lean_dec(v___x_3064_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3080_, 0, v_val_3076_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_val_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_stx_3055_);
v_val_3085_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3087_ = v___x_3063_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_val_3085_);
lean_dec(v___x_3063_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_val_3085_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3089_);
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_val_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_stx_3055_);
v_val_3094_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3096_ = v___x_3062_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_val_3094_);
lean_dec(v___x_3062_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3098_, 0, v_val_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_val_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_stx_3055_);
v_val_3103_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3105_ = v___x_3061_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_val_3103_);
lean_dec(v___x_3061_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
v___x_3107_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3107_, 0, v_val_3103_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3107_);
v___x_3109_ = v___x_3105_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_val_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_stx_3055_);
v_val_3112_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v___x_3060_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_val_3112_);
lean_dec(v___x_3060_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_val_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_object* v_val_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_stx_3055_);
v_val_3121_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3123_ = v___x_3059_;
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_val_3121_);
lean_dec(v___x_3059_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_val_3121_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3125_);
v___x_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v_val_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_stx_3055_);
v_val_3130_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3132_ = v___x_3058_;
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_val_3130_);
lean_dec(v___x_3058_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3134_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3134_, 0, v_val_3130_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3134_);
v___x_3136_ = v___x_3132_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_val_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_stx_3055_);
v_val_3139_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3141_ = v___x_3057_;
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_val_3139_);
lean_dec(v___x_3057_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3143_, 0, v_val_3139_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3143_);
v___x_3145_ = v___x_3141_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_val_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3156_; 
lean_dec(v_stx_3055_);
v_val_3148_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3150_ = v___x_3056_;
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_val_3148_);
lean_dec(v___x_3056_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3156_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_val_3148_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 0, v___x_3152_);
v___x_3154_ = v___x_3150_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(uint32_t v_a_3157_, lean_object* v_x_3158_){
_start:
{
if (lean_obj_tag(v_x_3158_) == 0)
{
uint8_t v___x_3159_; 
v___x_3159_ = 0;
return v___x_3159_;
}
else
{
lean_object* v_head_3160_; lean_object* v_tail_3161_; uint32_t v___x_3162_; uint8_t v___x_3163_; 
v_head_3160_ = lean_ctor_get(v_x_3158_, 0);
v_tail_3161_ = lean_ctor_get(v_x_3158_, 1);
v___x_3162_ = lean_unbox_uint32(v_head_3160_);
v___x_3163_ = lean_uint32_dec_eq(v_a_3157_, v___x_3162_);
if (v___x_3163_ == 0)
{
v_x_3158_ = v_tail_3161_;
goto _start;
}
else
{
return v___x_3163_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0___boxed(lean_object* v_a_3165_, lean_object* v_x_3166_){
_start:
{
uint32_t v_a_boxed_3167_; uint8_t v_res_3168_; lean_object* v_r_3169_; 
v_a_boxed_3167_ = lean_unbox_uint32(v_a_3165_);
lean_dec(v_a_3165_);
v_res_3168_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v_a_boxed_3167_, v_x_3166_);
lean_dec(v_x_3166_);
v_r_3169_ = lean_box(v_res_3168_);
return v_r_3169_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = 43;
v___x_3171_ = lean_box_uint32(v___x_3170_);
return v___x_3171_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__0(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_box(0);
v___x_3173_ = l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1;
v___x_3174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v___x_3172_);
return v___x_3174_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1(void){
_start:
{
uint32_t v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = 45;
v___x_3176_ = lean_box_uint32(v___x_3175_);
return v___x_3176_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__1(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__0, &l_Lean_Doc_UnorderedListItemView_of___closed__0_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__0);
v___x_3178_ = l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1;
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v___x_3177_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = 42;
v___x_3181_ = lean_box_uint32(v___x_3180_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_Doc_UnorderedListItemView_of___closed__2(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__1, &l_Lean_Doc_UnorderedListItemView_of___closed__1_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__1);
v___x_3183_ = l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1;
v___x_3184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v___x_3182_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListItemView_of(lean_object* v_stx_3185_){
_start:
{
lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__4));
lean_inc(v_stx_3185_);
v___x_3187_ = l_Lean_Syntax_isOfKind(v_stx_3185_, v___x_3186_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
lean_dec(v_stx_3185_);
v___x_3188_ = lean_box(0);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; lean_object* v_m_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3189_ = lean_unsigned_to_nat(0u);
v_m_3190_ = l_Lean_Syntax_getArg(v_stx_3185_, v___x_3189_);
v___x_3191_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__6));
lean_inc(v_m_3190_);
v___x_3192_ = l_Lean_Syntax_isOfKind(v_m_3190_, v___x_3191_);
if (v___x_3192_ == 0)
{
lean_object* v___x_3193_; 
lean_dec(v_m_3190_);
lean_dec(v_stx_3185_);
v___x_3193_ = lean_box(0);
return v___x_3193_;
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3194_ = l_Lean_TSyntax_getVersoDelimiter(v_m_3190_);
v___x_3195_ = lean_string_utf8_byte_size(v___x_3194_);
v___x_3196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3194_);
lean_ctor_set(v___x_3196_, 1, v___x_3189_);
lean_ctor_set(v___x_3196_, 2, v___x_3195_);
v___x_3197_ = l_String_Slice_Pos_get_x3f(v___x_3196_, v___x_3189_);
lean_dec_ref_known(v___x_3196_, 3);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v___x_3198_; 
lean_dec(v_m_3190_);
lean_dec(v_stx_3185_);
v___x_3198_ = lean_box(0);
return v___x_3198_;
}
else
{
lean_object* v_val_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3214_; 
v_val_3199_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3201_ = v___x_3197_;
v_isShared_3202_ = v_isSharedCheck_3214_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_val_3199_);
lean_dec(v___x_3197_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3214_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; uint32_t v___x_3204_; uint8_t v___x_3205_; 
v___x_3203_ = lean_obj_once(&l_Lean_Doc_UnorderedListItemView_of___closed__2, &l_Lean_Doc_UnorderedListItemView_of___closed__2_once, _init_l_Lean_Doc_UnorderedListItemView_of___closed__2);
v___x_3204_ = lean_unbox_uint32(v_val_3199_);
lean_dec(v_val_3199_);
v___x_3205_ = l_List_elem___at___00Lean_Doc_UnorderedListItemView_of_spec__0(v___x_3204_, v___x_3203_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; 
lean_del_object(v___x_3201_);
lean_dec(v_m_3190_);
lean_dec(v_stx_3185_);
v___x_3206_ = lean_box(0);
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v_bs_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3207_ = lean_unsigned_to_nat(1u);
v___x_3208_ = l_Lean_Syntax_getArg(v_stx_3185_, v___x_3207_);
v_bs_3209_ = l_Lean_Syntax_getArgs(v___x_3208_);
lean_dec(v___x_3208_);
v___x_3210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3210_, 0, v_stx_3185_);
lean_ctor_set(v___x_3210_, 1, v_m_3190_);
lean_ctor_set(v___x_3210_, 2, v_bs_3209_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3210_);
v___x_3212_ = v___x_3201_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(lean_object* v_s_3215_, lean_object* v_pos_3216_){
_start:
{
lean_object* v_str_3217_; lean_object* v_startInclusive_3218_; lean_object* v_endExclusive_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v_decide_3223_; 
v_str_3217_ = lean_ctor_get(v_s_3215_, 0);
v_startInclusive_3218_ = lean_ctor_get(v_s_3215_, 1);
v_endExclusive_3219_ = lean_ctor_get(v_s_3215_, 2);
v___x_3220_ = lean_nat_add(v_startInclusive_3218_, v_pos_3216_);
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = lean_nat_sub(v_endExclusive_3219_, v___x_3220_);
v_decide_3223_ = lean_nat_dec_eq(v___x_3221_, v___x_3222_);
lean_dec(v___x_3222_);
if (v_decide_3223_ == 0)
{
uint32_t v___x_3224_; uint32_t v___x_3225_; uint8_t v___x_3226_; 
v___x_3224_ = lean_string_utf8_get_fast(v_str_3217_, v___x_3220_);
v___x_3225_ = 48;
v___x_3226_ = lean_uint32_dec_le(v___x_3225_, v___x_3224_);
if (v___x_3226_ == 0)
{
lean_dec(v___x_3220_);
return v_pos_3216_;
}
else
{
uint32_t v___x_3227_; uint8_t v___x_3228_; 
v___x_3227_ = 57;
v___x_3228_ = lean_uint32_dec_le(v___x_3224_, v___x_3227_);
if (v___x_3228_ == 0)
{
lean_dec(v___x_3220_);
return v_pos_3216_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v___x_3229_ = lean_string_utf8_next_fast(v_str_3217_, v___x_3220_);
v___x_3230_ = lean_nat_sub(v___x_3229_, v___x_3220_);
lean_dec(v___x_3220_);
v___x_3231_ = lean_nat_add(v_pos_3216_, v___x_3230_);
lean_dec(v___x_3230_);
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = lean_nat_add(v_pos_3216_, v___x_3232_);
v___x_3234_ = lean_nat_dec_le(v___x_3233_, v___x_3231_);
lean_dec(v___x_3233_);
if (v___x_3234_ == 0)
{
lean_dec(v___x_3231_);
return v_pos_3216_;
}
else
{
lean_dec(v_pos_3216_);
v_pos_3216_ = v___x_3231_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_3220_);
return v_pos_3216_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0___boxed(lean_object* v_s_3236_, lean_object* v_pos_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v_s_3236_, v_pos_3237_);
lean_dec_ref(v_s_3236_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_number(lean_object* v_v_3239_){
_start:
{
lean_object* v_marker_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3255_; 
v_marker_3240_ = lean_ctor_get(v_v_3239_, 1);
v_isSharedCheck_3255_ = !lean_is_exclusive(v_v_3239_);
if (v_isSharedCheck_3255_ == 0)
{
lean_object* v_unused_3256_; lean_object* v_unused_3257_; 
v_unused_3256_ = lean_ctor_get(v_v_3239_, 2);
lean_dec(v_unused_3256_);
v_unused_3257_ = lean_ctor_get(v_v_3239_, 0);
lean_dec(v_unused_3257_);
v___x_3242_ = v_v_3239_;
v_isShared_3243_ = v_isSharedCheck_3255_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_marker_3240_);
lean_dec(v_v_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3255_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3244_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_3240_);
lean_dec(v_marker_3240_);
v___x_3245_ = lean_unsigned_to_nat(0u);
v___x_3246_ = lean_string_utf8_byte_size(v___x_3244_);
lean_inc_ref(v___x_3244_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 2, v___x_3246_);
lean_ctor_set(v___x_3242_, 1, v___x_3245_);
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3248_ = v___x_3242_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3249_ = l_String_Slice_Pos_skipWhile___at___00Lean_Doc_OrderedListItemView_number_spec__0(v___x_3248_, v___x_3245_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = lean_string_utf8_extract_fast(v___x_3244_, v___x_3245_, v___x_3249_);
lean_dec(v___x_3249_);
lean_dec_ref(v___x_3244_);
v___x_3251_ = lean_string_utf8_byte_size(v___x_3250_);
v___x_3252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3245_);
lean_ctor_set(v___x_3252_, 2, v___x_3251_);
v___x_3253_ = l_String_Slice_toNat_x3f(v___x_3252_);
lean_dec_ref_known(v___x_3252_, 3);
return v___x_3253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListItemView_of(lean_object* v_stx_3258_){
_start:
{
lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__4));
lean_inc(v_stx_3258_);
v___x_3260_ = l_Lean_Syntax_isOfKind(v_stx_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; 
lean_dec(v_stx_3258_);
v___x_3261_ = lean_box(0);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v_m_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3262_ = lean_unsigned_to_nat(0u);
v_m_3263_ = l_Lean_Syntax_getArg(v_stx_3258_, v___x_3262_);
v___x_3264_ = ((lean_object*)(l_Lean_Doc_listItemToParser___closed__6));
lean_inc(v_m_3263_);
v___x_3265_ = l_Lean_Syntax_isOfKind(v_m_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; 
lean_dec(v_m_3263_);
lean_dec(v_stx_3258_);
v___x_3266_ = lean_box(0);
return v___x_3266_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3267_ = l_Lean_TSyntax_getVersoDelimiter(v_m_3263_);
v___x_3268_ = lean_string_utf8_byte_size(v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3262_);
lean_ctor_set(v___x_3269_, 2, v___x_3268_);
v___x_3270_ = l_String_Slice_Pos_get_x3f(v___x_3269_, v___x_3262_);
lean_dec_ref_known(v___x_3269_, 3);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3271_; 
lean_dec(v_m_3263_);
lean_dec(v_stx_3258_);
v___x_3271_ = lean_box(0);
return v___x_3271_;
}
else
{
lean_object* v_val_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3291_; 
v_val_3272_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3274_ = v___x_3270_;
v_isShared_3275_ = v_isSharedCheck_3291_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_val_3272_);
lean_dec(v___x_3270_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3291_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
uint32_t v___x_3276_; uint32_t v___x_3277_; uint8_t v___x_3278_; 
v___x_3276_ = 48;
v___x_3277_ = lean_unbox_uint32(v_val_3272_);
v___x_3278_ = lean_uint32_dec_le(v___x_3276_, v___x_3277_);
if (v___x_3278_ == 0)
{
lean_object* v___x_3279_; 
lean_del_object(v___x_3274_);
lean_dec(v_val_3272_);
lean_dec(v_m_3263_);
lean_dec(v_stx_3258_);
v___x_3279_ = lean_box(0);
return v___x_3279_;
}
else
{
uint32_t v___x_3280_; uint32_t v___x_3281_; uint8_t v___x_3282_; 
v___x_3280_ = 57;
v___x_3281_ = lean_unbox_uint32(v_val_3272_);
lean_dec(v_val_3272_);
v___x_3282_ = lean_uint32_dec_le(v___x_3281_, v___x_3280_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; 
lean_del_object(v___x_3274_);
lean_dec(v_m_3263_);
lean_dec(v_stx_3258_);
v___x_3283_ = lean_box(0);
return v___x_3283_;
}
else
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_bs_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3284_ = lean_unsigned_to_nat(1u);
v___x_3285_ = l_Lean_Syntax_getArg(v_stx_3258_, v___x_3284_);
v_bs_3286_ = l_Lean_Syntax_getArgs(v___x_3285_);
lean_dec(v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3287_, 0, v_stx_3258_);
lean_ctor_set(v___x_3287_, 1, v_m_3263_);
lean_ctor_set(v___x_3287_, 2, v_bs_3286_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3287_);
v___x_3289_ = v___x_3274_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescItemView_of(lean_object* v_stx_3292_){
_start:
{
lean_object* v___x_3293_; uint8_t v___x_3294_; 
v___x_3293_ = ((lean_object*)(l_Lean_Doc_descItemToParser___closed__3));
lean_inc(v_stx_3292_);
v___x_3294_ = l_Lean_Syntax_isOfKind(v_stx_3292_, v___x_3293_);
if (v___x_3294_ == 0)
{
lean_object* v___x_3295_; 
lean_dec(v_stx_3292_);
v___x_3295_ = lean_box(0);
return v___x_3295_;
}
else
{
lean_object* v___x_3296_; lean_object* v_marker_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v_desc_3302_; lean_object* v_term_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3296_ = lean_unsigned_to_nat(0u);
v_marker_3297_ = l_Lean_Syntax_getArg(v_stx_3292_, v___x_3296_);
v___x_3298_ = lean_unsigned_to_nat(1u);
v___x_3299_ = l_Lean_Syntax_getArg(v_stx_3292_, v___x_3298_);
v___x_3300_ = lean_unsigned_to_nat(2u);
v___x_3301_ = l_Lean_Syntax_getArg(v_stx_3292_, v___x_3300_);
v_desc_3302_ = l_Lean_Syntax_getArgs(v___x_3301_);
lean_dec(v___x_3301_);
v_term_3303_ = l_Lean_Syntax_getArgs(v___x_3299_);
lean_dec(v___x_3299_);
v___x_3304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3304_, 0, v_stx_3292_);
lean_ctor_set(v___x_3304_, 1, v_marker_3297_);
lean_ctor_set(v___x_3304_, 2, v_term_3303_);
lean_ctor_set(v___x_3304_, 3, v_desc_3302_);
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_ParaView_of(lean_object* v_stx_3306_){
_start:
{
lean_object* v___x_3307_; uint8_t v___x_3308_; 
v___x_3307_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__43));
lean_inc(v_stx_3306_);
v___x_3308_ = l_Lean_Syntax_isOfKind(v_stx_3306_, v___x_3307_);
if (v___x_3308_ == 0)
{
lean_object* v___x_3309_; 
lean_dec(v_stx_3306_);
v___x_3309_ = lean_box(0);
return v___x_3309_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_inl_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3310_ = lean_unsigned_to_nat(0u);
v___x_3311_ = l_Lean_Syntax_getArg(v_stx_3306_, v___x_3310_);
v_inl_3312_ = l_Lean_Syntax_getArgs(v___x_3311_);
lean_dec(v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v_stx_3306_);
lean_ctor_set(v___x_3313_, 1, v_inl_3312_);
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
return v___x_3314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(size_t v_sz_3315_, size_t v_i_3316_, lean_object* v_bs_3317_){
_start:
{
uint8_t v___x_3318_; 
v___x_3318_ = lean_usize_dec_lt(v_i_3316_, v_sz_3315_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_bs_3317_);
return v___x_3319_;
}
else
{
lean_object* v_v_3320_; lean_object* v___x_3321_; 
v_v_3320_ = lean_array_uget_borrowed(v_bs_3317_, v_i_3316_);
lean_inc(v_v_3320_);
v___x_3321_ = l_Lean_Doc_UnorderedListItemView_of(v_v_3320_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v_bs_3317_);
v___x_3322_ = lean_box(0);
return v___x_3322_;
}
else
{
lean_object* v_val_3323_; lean_object* v___x_3324_; lean_object* v_bs_x27_3325_; size_t v___x_3326_; size_t v___x_3327_; lean_object* v___x_3328_; 
v_val_3323_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_val_3323_);
lean_dec_ref_known(v___x_3321_, 1);
v___x_3324_ = lean_unsigned_to_nat(0u);
v_bs_x27_3325_ = lean_array_uset(v_bs_3317_, v_i_3316_, v___x_3324_);
v___x_3326_ = ((size_t)1ULL);
v___x_3327_ = lean_usize_add(v_i_3316_, v___x_3326_);
v___x_3328_ = lean_array_uset(v_bs_x27_3325_, v_i_3316_, v_val_3323_);
v_i_3316_ = v___x_3327_;
v_bs_3317_ = v___x_3328_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0___boxed(lean_object* v_sz_3330_, lean_object* v_i_3331_, lean_object* v_bs_3332_){
_start:
{
size_t v_sz_boxed_3333_; size_t v_i_boxed_3334_; lean_object* v_res_3335_; 
v_sz_boxed_3333_ = lean_unbox_usize(v_sz_3330_);
lean_dec(v_sz_3330_);
v_i_boxed_3334_ = lean_unbox_usize(v_i_3331_);
lean_dec(v_i_3331_);
v_res_3335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_boxed_3333_, v_i_boxed_3334_, v_bs_3332_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_UnorderedListView_of(lean_object* v_stx_3336_){
_start:
{
lean_object* v___x_3337_; uint8_t v___x_3338_; 
v___x_3337_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__41));
lean_inc(v_stx_3336_);
v___x_3338_ = l_Lean_Syntax_isOfKind(v_stx_3336_, v___x_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; 
lean_dec(v_stx_3336_);
v___x_3339_ = lean_box(0);
return v___x_3339_;
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v_items_3342_; size_t v_sz_3343_; size_t v___x_3344_; lean_object* v___x_3345_; 
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = l_Lean_Syntax_getArg(v_stx_3336_, v___x_3340_);
v_items_3342_ = l_Lean_Syntax_getArgs(v___x_3341_);
lean_dec(v___x_3341_);
v_sz_3343_ = lean_array_size(v_items_3342_);
v___x_3344_ = ((size_t)0ULL);
v___x_3345_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_UnorderedListView_of_spec__0(v_sz_3343_, v___x_3344_, v_items_3342_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; 
lean_dec(v_stx_3336_);
v___x_3346_ = lean_box(0);
return v___x_3346_;
}
else
{
lean_object* v_val_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3355_; 
v_val_3347_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3349_ = v___x_3345_;
v_isShared_3350_ = v_isSharedCheck_3355_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_val_3347_);
lean_dec(v___x_3345_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3355_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v_stx_3336_);
lean_ctor_set(v___x_3351_, 1, v_val_3347_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3351_);
v___x_3353_ = v___x_3349_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(size_t v_sz_3356_, size_t v_i_3357_, lean_object* v_bs_3358_){
_start:
{
uint8_t v___x_3359_; 
v___x_3359_ = lean_usize_dec_lt(v_i_3357_, v_sz_3356_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_bs_3358_);
return v___x_3360_;
}
else
{
lean_object* v_v_3361_; lean_object* v___x_3362_; 
v_v_3361_ = lean_array_uget_borrowed(v_bs_3358_, v_i_3357_);
lean_inc(v_v_3361_);
v___x_3362_ = l_Lean_Doc_OrderedListItemView_of(v_v_3361_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v___x_3363_; 
lean_dec_ref(v_bs_3358_);
v___x_3363_ = lean_box(0);
return v___x_3363_;
}
else
{
lean_object* v_val_3364_; lean_object* v___x_3365_; lean_object* v_bs_x27_3366_; size_t v___x_3367_; size_t v___x_3368_; lean_object* v___x_3369_; 
v_val_3364_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_val_3364_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3365_ = lean_unsigned_to_nat(0u);
v_bs_x27_3366_ = lean_array_uset(v_bs_3358_, v_i_3357_, v___x_3365_);
v___x_3367_ = ((size_t)1ULL);
v___x_3368_ = lean_usize_add(v_i_3357_, v___x_3367_);
v___x_3369_ = lean_array_uset(v_bs_x27_3366_, v_i_3357_, v_val_3364_);
v_i_3357_ = v___x_3368_;
v_bs_3358_ = v___x_3369_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0___boxed(lean_object* v_sz_3371_, lean_object* v_i_3372_, lean_object* v_bs_3373_){
_start:
{
size_t v_sz_boxed_3374_; size_t v_i_boxed_3375_; lean_object* v_res_3376_; 
v_sz_boxed_3374_ = lean_unbox_usize(v_sz_3371_);
lean_dec(v_sz_3371_);
v_i_boxed_3375_ = lean_unbox_usize(v_i_3372_);
lean_dec(v_i_3372_);
v_res_3376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_boxed_3374_, v_i_boxed_3375_, v_bs_3373_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_OrderedListView_of(lean_object* v_stx_3377_){
_start:
{
lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__40));
lean_inc(v_stx_3377_);
v___x_3379_ = l_Lean_Syntax_isOfKind(v_stx_3377_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; 
lean_dec(v_stx_3377_);
v___x_3380_ = lean_box(0);
return v___x_3380_;
}
else
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v_items_3383_; size_t v_sz_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = l_Lean_Syntax_getArg(v_stx_3377_, v___x_3381_);
v_items_3383_ = l_Lean_Syntax_getArgs(v___x_3382_);
lean_dec(v___x_3382_);
v_sz_3384_ = lean_array_size(v_items_3383_);
v___x_3385_ = ((size_t)0ULL);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_OrderedListView_of_spec__0(v_sz_3384_, v___x_3385_, v_items_3383_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v___x_3387_; 
lean_dec(v_stx_3377_);
v___x_3387_ = lean_box(0);
return v___x_3387_;
}
else
{
lean_object* v_val_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3405_; 
v_val_3388_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3390_ = v___x_3386_;
v_isShared_3391_ = v_isSharedCheck_3405_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_val_3388_);
lean_dec(v___x_3386_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3405_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___y_3393_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v___x_3400_ = lean_array_get_size(v_val_3388_);
v___x_3401_ = lean_nat_dec_lt(v___x_3381_, v___x_3400_);
if (v___x_3401_ == 0)
{
goto v___jp_3398_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = lean_array_fget_borrowed(v_val_3388_, v___x_3381_);
lean_inc(v___x_3402_);
v___x_3403_ = l_Lean_Doc_OrderedListItemView_number(v___x_3402_);
if (lean_obj_tag(v___x_3403_) == 0)
{
goto v___jp_3398_;
}
else
{
lean_object* v_val_3404_; 
v_val_3404_ = lean_ctor_get(v___x_3403_, 0);
lean_inc(v_val_3404_);
lean_dec_ref_known(v___x_3403_, 1);
v___y_3393_ = v_val_3404_;
goto v___jp_3392_;
}
}
v___jp_3392_:
{
lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3394_, 0, v_stx_3377_);
lean_ctor_set(v___x_3394_, 1, v___y_3393_);
lean_ctor_set(v___x_3394_, 2, v_val_3388_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3394_);
v___x_3396_ = v___x_3390_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3394_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
v___jp_3398_:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_unsigned_to_nat(1u);
v___y_3393_ = v___x_3399_;
goto v___jp_3392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(size_t v_sz_3406_, size_t v_i_3407_, lean_object* v_bs_3408_){
_start:
{
uint8_t v___x_3409_; 
v___x_3409_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3410_, 0, v_bs_3408_);
return v___x_3410_;
}
else
{
lean_object* v_v_3411_; lean_object* v___x_3412_; 
v_v_3411_ = lean_array_uget_borrowed(v_bs_3408_, v_i_3407_);
lean_inc(v_v_3411_);
v___x_3412_ = l_Lean_Doc_DescItemView_of(v_v_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v___x_3413_; 
lean_dec_ref(v_bs_3408_);
v___x_3413_ = lean_box(0);
return v___x_3413_;
}
else
{
lean_object* v_val_3414_; lean_object* v___x_3415_; lean_object* v_bs_x27_3416_; size_t v___x_3417_; size_t v___x_3418_; lean_object* v___x_3419_; 
v_val_3414_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_val_3414_);
lean_dec_ref_known(v___x_3412_, 1);
v___x_3415_ = lean_unsigned_to_nat(0u);
v_bs_x27_3416_ = lean_array_uset(v_bs_3408_, v_i_3407_, v___x_3415_);
v___x_3417_ = ((size_t)1ULL);
v___x_3418_ = lean_usize_add(v_i_3407_, v___x_3417_);
v___x_3419_ = lean_array_uset(v_bs_x27_3416_, v_i_3407_, v_val_3414_);
v_i_3407_ = v___x_3418_;
v_bs_3408_ = v___x_3419_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0___boxed(lean_object* v_sz_3421_, lean_object* v_i_3422_, lean_object* v_bs_3423_){
_start:
{
size_t v_sz_boxed_3424_; size_t v_i_boxed_3425_; lean_object* v_res_3426_; 
v_sz_boxed_3424_ = lean_unbox_usize(v_sz_3421_);
lean_dec(v_sz_3421_);
v_i_boxed_3425_ = lean_unbox_usize(v_i_3422_);
lean_dec(v_i_3422_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_boxed_3424_, v_i_boxed_3425_, v_bs_3423_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DescListView_of(lean_object* v_stx_3427_){
_start:
{
lean_object* v___x_3428_; uint8_t v___x_3429_; 
v___x_3428_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__39));
lean_inc(v_stx_3427_);
v___x_3429_ = l_Lean_Syntax_isOfKind(v_stx_3427_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v_stx_3427_);
v___x_3430_ = lean_box(0);
return v___x_3430_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v_items_3433_; size_t v_sz_3434_; size_t v___x_3435_; lean_object* v___x_3436_; 
v___x_3431_ = lean_unsigned_to_nat(0u);
v___x_3432_ = l_Lean_Syntax_getArg(v_stx_3427_, v___x_3431_);
v_items_3433_ = l_Lean_Syntax_getArgs(v___x_3432_);
lean_dec(v___x_3432_);
v_sz_3434_ = lean_array_size(v_items_3433_);
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_DescListView_of_spec__0(v_sz_3434_, v___x_3435_, v_items_3433_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v___x_3437_; 
lean_dec(v_stx_3427_);
v___x_3437_ = lean_box(0);
return v___x_3437_;
}
else
{
lean_object* v_val_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3446_; 
v_val_3438_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3440_ = v___x_3436_;
v_isShared_3441_ = v_isSharedCheck_3446_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_val_3438_);
lean_dec(v___x_3436_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3446_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3442_, 0, v_stx_3427_);
lean_ctor_set(v___x_3442_, 1, v_val_3438_);
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3442_);
v___x_3444_ = v___x_3440_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockquoteView_of(lean_object* v_stx_3447_){
_start:
{
lean_object* v___x_3448_; uint8_t v___x_3449_; 
v___x_3448_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__42));
lean_inc(v_stx_3447_);
v___x_3449_ = l_Lean_Syntax_isOfKind(v_stx_3447_, v___x_3448_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; 
lean_dec(v_stx_3447_);
v___x_3450_ = lean_box(0);
return v___x_3450_;
}
else
{
lean_object* v___x_3451_; lean_object* v_gt_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v_bs_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v_gt_3452_ = l_Lean_Syntax_getArg(v_stx_3447_, v___x_3451_);
v___x_3453_ = lean_unsigned_to_nat(1u);
v___x_3454_ = l_Lean_Syntax_getArg(v_stx_3447_, v___x_3453_);
v_bs_3455_ = l_Lean_Syntax_getArgs(v___x_3454_);
lean_dec(v___x_3454_);
v___x_3456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3456_, 0, v_stx_3447_);
lean_ctor_set(v___x_3456_, 1, v_gt_3452_);
lean_ctor_set(v___x_3456_, 2, v_bs_3455_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock(lean_object* v_v_3458_){
_start:
{
lean_object* v_content_3459_; lean_object* v___x_3460_; 
v_content_3459_ = lean_ctor_get(v_v_3458_, 4);
v___x_3460_ = l_Lean_TSyntax_getVersoCodeBlock(v_content_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_getVersoCodeBlock___boxed(lean_object* v_v_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Doc_CodeBlockView_getVersoCodeBlock(v_v_3461_);
lean_dec_ref(v_v_3461_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CodeBlockView_of(lean_object* v_stx_3469_){
_start:
{
lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3470_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__36));
lean_inc(v_stx_3469_);
v___x_3471_ = l_Lean_Syntax_isOfKind(v_stx_3469_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3472_; 
lean_dec(v_stx_3469_);
v___x_3472_ = lean_box(0);
return v___x_3472_;
}
else
{
lean_object* v___x_3473_; lean_object* v_openFence_3474_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v_name_3497_; lean_object* v_args_3498_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3473_ = lean_unsigned_to_nat(0u);
v_openFence_3474_ = l_Lean_Syntax_getArg(v_stx_3469_, v___x_3473_);
v___x_3511_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1));
lean_inc(v_openFence_3474_);
v___x_3512_ = l_Lean_Syntax_isOfKind(v_openFence_3474_, v___x_3511_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; 
lean_dec(v_openFence_3474_);
lean_dec(v_stx_3469_);
v___x_3513_ = lean_box(0);
return v___x_3513_;
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; 
v___x_3514_ = lean_unsigned_to_nat(1u);
v___x_3515_ = l_Lean_Syntax_getArg(v_stx_3469_, v___x_3514_);
v___x_3516_ = l_Lean_Syntax_isNone(v___x_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3517_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3515_);
v___x_3518_ = l_Lean_Syntax_matchesNull(v___x_3515_, v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
lean_dec(v___x_3515_);
lean_dec(v_openFence_3474_);
lean_dec(v_stx_3469_);
v___x_3519_ = lean_box(0);
return v___x_3519_;
}
else
{
lean_object* v_name_3520_; 
v_name_3520_ = l_Lean_Syntax_getArg(v___x_3515_, v___x_3473_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_3520_);
v___x_3527_ = l_Lean_Syntax_isOfKind(v_name_3520_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_dec(v_name_3520_);
lean_dec(v___x_3515_);
lean_dec(v_openFence_3474_);
lean_dec(v_stx_3469_);
v___x_3528_ = lean_box(0);
return v___x_3528_;
}
else
{
goto v___jp_3521_;
}
}
else
{
goto v___jp_3521_;
}
v___jp_3521_:
{
lean_object* v___x_3522_; lean_object* v_args_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3522_ = l_Lean_Syntax_getArg(v___x_3515_, v___x_3514_);
lean_dec(v___x_3515_);
v_args_3523_ = l_Lean_Syntax_getArgs(v___x_3522_);
lean_dec(v___x_3522_);
v___x_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3524_, 0, v_name_3520_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_args_3523_);
v_name_3497_ = v___x_3524_;
v_args_3498_ = v___x_3525_;
goto v___jp_3496_;
}
}
}
else
{
lean_object* v___x_3529_; 
lean_dec(v___x_3515_);
v___x_3529_ = lean_box(0);
v_name_3497_ = v___x_3529_;
v_args_3498_ = v___x_3529_;
goto v___jp_3496_;
}
}
v___jp_3475_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3480_, 0, v_stx_3469_);
lean_ctor_set(v___x_3480_, 1, v_openFence_3474_);
lean_ctor_set(v___x_3480_, 2, v___y_3477_);
lean_ctor_set(v___x_3480_, 3, v___y_3479_);
lean_ctor_set(v___x_3480_, 4, v___y_3478_);
lean_ctor_set(v___x_3480_, 5, v___y_3476_);
v___x_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
return v___x_3481_;
}
v___jp_3482_:
{
if (lean_obj_tag(v___y_3485_) == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__37));
v___y_3476_ = v___y_3483_;
v___y_3477_ = v___y_3484_;
v___y_3478_ = v___y_3486_;
v___y_3479_ = v___x_3487_;
goto v___jp_3475_;
}
else
{
lean_object* v_val_3488_; 
v_val_3488_ = lean_ctor_get(v___y_3485_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v___y_3485_, 1);
v___y_3476_ = v___y_3483_;
v___y_3477_ = v___y_3484_;
v___y_3478_ = v___y_3486_;
v___y_3479_ = v_val_3488_;
goto v___jp_3475_;
}
}
v___jp_3489_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = l___private_Lean_DocString_View_0__Lean_Doc_emptyContentInfo(v___y_3490_);
v___x_3495_ = l_Lean_Syntax_setInfo(v___x_3494_, v___y_3492_);
v___y_3483_ = v___y_3490_;
v___y_3484_ = v___y_3491_;
v___y_3485_ = v___y_3493_;
v___y_3486_ = v___x_3495_;
goto v___jp_3482_;
}
v___jp_3496_:
{
lean_object* v___x_3499_; lean_object* v_s_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v___x_3499_ = lean_unsigned_to_nat(2u);
v_s_3500_ = l_Lean_Syntax_getArg(v_stx_3469_, v___x_3499_);
v___x_3501_ = ((lean_object*)(l_Lean_Doc_CodeBlockView_of___closed__1));
lean_inc(v_s_3500_);
v___x_3502_ = l_Lean_Syntax_isOfKind(v_s_3500_, v___x_3501_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; 
lean_dec(v_s_3500_);
lean_dec(v_args_3498_);
lean_dec(v_name_3497_);
lean_dec(v_openFence_3474_);
lean_dec(v_stx_3469_);
v___x_3503_ = lean_box(0);
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; lean_object* v_closeFence_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3504_ = lean_unsigned_to_nat(3u);
v_closeFence_3505_ = l_Lean_Syntax_getArg(v_stx_3469_, v___x_3504_);
v___x_3506_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asFence___closed__1));
lean_inc(v_closeFence_3505_);
v___x_3507_ = l_Lean_Syntax_isOfKind(v_closeFence_3505_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v_closeFence_3505_);
lean_dec(v_s_3500_);
lean_dec(v_args_3498_);
lean_dec(v_name_3497_);
lean_dec(v_openFence_3474_);
lean_dec(v_stx_3469_);
v___x_3508_ = lean_box(0);
return v___x_3508_;
}
else
{
uint8_t v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = 0;
v___x_3510_ = l_Lean_Syntax_getPos_x3f(v_s_3500_, v___x_3509_);
if (lean_obj_tag(v___x_3510_) == 0)
{
v___y_3490_ = v_closeFence_3505_;
v___y_3491_ = v_name_3497_;
v___y_3492_ = v_s_3500_;
v___y_3493_ = v_args_3498_;
goto v___jp_3489_;
}
else
{
lean_dec_ref_known(v___x_3510_, 1);
if (v___x_3471_ == 0)
{
v___y_3490_ = v_closeFence_3505_;
v___y_3491_ = v_name_3497_;
v___y_3492_ = v_s_3500_;
v___y_3493_ = v_args_3498_;
goto v___jp_3489_;
}
else
{
v___y_3483_ = v_closeFence_3505_;
v___y_3484_ = v_name_3497_;
v___y_3485_ = v_args_3498_;
v___y_3486_ = v_s_3500_;
goto v___jp_3482_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_DirectiveView_of(lean_object* v_stx_3530_){
_start:
{
lean_object* v___x_3531_; uint8_t v___x_3532_; 
v___x_3531_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__35));
lean_inc(v_stx_3530_);
v___x_3532_ = l_Lean_Syntax_isOfKind(v_stx_3530_, v___x_3531_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; 
lean_dec(v_stx_3530_);
v___x_3533_ = lean_box(0);
return v___x_3533_;
}
else
{
lean_object* v___x_3534_; lean_object* v_opener_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v___x_3534_ = lean_unsigned_to_nat(0u);
v_opener_3535_ = l_Lean_Syntax_getArg(v_stx_3530_, v___x_3534_);
v___x_3536_ = ((lean_object*)(l___private_Lean_DocString_View_0__Lean_Doc_asDirectiveDelimiter___closed__1));
lean_inc(v_opener_3535_);
v___x_3537_ = l_Lean_Syntax_isOfKind(v_opener_3535_, v___x_3536_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; 
lean_dec(v_opener_3535_);
lean_dec(v_stx_3530_);
v___x_3538_ = lean_box(0);
return v___x_3538_;
}
else
{
lean_object* v___x_3539_; lean_object* v_name_3540_; lean_object* v___x_3541_; uint8_t v___x_3542_; 
v___x_3539_ = lean_unsigned_to_nat(1u);
v_name_3540_ = l_Lean_Syntax_getArg(v_stx_3530_, v___x_3539_);
v___x_3541_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_3540_);
v___x_3542_ = l_Lean_Syntax_isOfKind(v_name_3540_, v___x_3541_);
if (v___x_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec(v_name_3540_);
lean_dec(v_opener_3535_);
lean_dec(v_stx_3530_);
v___x_3543_ = lean_box(0);
return v___x_3543_;
}
else
{
lean_object* v___x_3544_; lean_object* v_closer_3545_; uint8_t v___x_3546_; 
v___x_3544_ = lean_unsigned_to_nat(4u);
v_closer_3545_ = l_Lean_Syntax_getArg(v_stx_3530_, v___x_3544_);
lean_inc(v_closer_3545_);
v___x_3546_ = l_Lean_Syntax_isOfKind(v_closer_3545_, v___x_3536_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec(v_closer_3545_);
lean_dec(v_name_3540_);
lean_dec(v_opener_3535_);
lean_dec(v_stx_3530_);
v___x_3547_ = lean_box(0);
return v___x_3547_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v_bs_3552_; lean_object* v_args_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3548_ = lean_unsigned_to_nat(2u);
v___x_3549_ = l_Lean_Syntax_getArg(v_stx_3530_, v___x_3548_);
v___x_3550_ = lean_unsigned_to_nat(3u);
v___x_3551_ = l_Lean_Syntax_getArg(v_stx_3530_, v___x_3550_);
v_bs_3552_ = l_Lean_Syntax_getArgs(v___x_3551_);
lean_dec(v___x_3551_);
v_args_3553_ = l_Lean_Syntax_getArgs(v___x_3549_);
lean_dec(v___x_3549_);
v___x_3554_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3554_, 0, v_stx_3530_);
lean_ctor_set(v___x_3554_, 1, v_opener_3535_);
lean_ctor_set(v___x_3554_, 2, v_name_3540_);
lean_ctor_set(v___x_3554_, 3, v_args_3553_);
lean_ctor_set(v___x_3554_, 4, v_bs_3552_);
lean_ctor_set(v___x_3554_, 5, v_closer_3545_);
v___x_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
return v___x_3555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_CommandView_of(lean_object* v_stx_3556_){
_start:
{
lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__34));
lean_inc(v_stx_3556_);
v___x_3558_ = l_Lean_Syntax_isOfKind(v_stx_3556_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; 
lean_dec(v_stx_3556_);
v___x_3559_ = lean_box(0);
return v___x_3559_;
}
else
{
lean_object* v___x_3560_; lean_object* v_name_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3560_ = lean_unsigned_to_nat(1u);
v_name_3561_ = l_Lean_Syntax_getArg(v_stx_3556_, v___x_3560_);
v___x_3562_ = ((lean_object*)(l_Lean_Doc_ArgValView_of___closed__12));
lean_inc(v_name_3561_);
v___x_3563_ = l_Lean_Syntax_isOfKind(v_name_3561_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_dec(v_name_3561_);
lean_dec(v_stx_3556_);
v___x_3564_ = lean_box(0);
return v___x_3564_;
}
else
{
lean_object* v___x_3565_; lean_object* v_braceOpen_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v_braceClose_3570_; lean_object* v_args_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3565_ = lean_unsigned_to_nat(0u);
v_braceOpen_3566_ = l_Lean_Syntax_getArg(v_stx_3556_, v___x_3565_);
v___x_3567_ = lean_unsigned_to_nat(2u);
v___x_3568_ = l_Lean_Syntax_getArg(v_stx_3556_, v___x_3567_);
v___x_3569_ = lean_unsigned_to_nat(3u);
v_braceClose_3570_ = l_Lean_Syntax_getArg(v_stx_3556_, v___x_3569_);
v_args_3571_ = l_Lean_Syntax_getArgs(v___x_3568_);
lean_dec(v___x_3568_);
v___x_3572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3572_, 0, v_stx_3556_);
lean_ctor_set(v___x_3572_, 1, v_braceOpen_3566_);
lean_ctor_set(v___x_3572_, 2, v_name_3561_);
lean_ctor_set(v___x_3572_, 3, v_args_3571_);
lean_ctor_set(v___x_3572_, 4, v_braceClose_3570_);
v___x_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_HeaderView_of(lean_object* v_stx_3574_){
_start:
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__31));
lean_inc(v_stx_3574_);
v___x_3576_ = l_Lean_Syntax_isOfKind(v_stx_3574_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; 
lean_dec(v_stx_3574_);
v___x_3577_ = lean_box(0);
return v___x_3577_;
}
else
{
lean_object* v___x_3578_; lean_object* v_marker_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3578_ = lean_unsigned_to_nat(0u);
v_marker_3579_ = l_Lean_Syntax_getArg(v_stx_3574_, v___x_3578_);
v___x_3580_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__33));
lean_inc(v_marker_3579_);
v___x_3581_ = l_Lean_Syntax_isOfKind(v_marker_3579_, v___x_3580_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; 
lean_dec(v_marker_3579_);
lean_dec(v_stx_3574_);
v___x_3582_ = lean_box(0);
return v___x_3582_;
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v_content_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3583_ = lean_unsigned_to_nat(1u);
v___x_3584_ = l_Lean_Syntax_getArg(v_stx_3574_, v___x_3583_);
v_content_3585_ = l_Lean_Syntax_getArgs(v___x_3584_);
lean_dec(v___x_3584_);
v___x_3586_ = l_Lean_TSyntax_getVersoDelimiter(v_marker_3579_);
v___x_3587_ = lean_string_length(v___x_3586_);
lean_dec_ref(v___x_3586_);
v___x_3588_ = lean_nat_sub(v___x_3587_, v___x_3583_);
v___x_3589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3589_, 0, v_stx_3574_);
lean_ctor_set(v___x_3589_, 1, v_marker_3579_);
lean_ctor_set(v___x_3589_, 2, v___x_3588_);
lean_ctor_set(v___x_3589_, 3, v_content_3585_);
v___x_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName(lean_object* v_v_3591_){
_start:
{
lean_object* v_name_3592_; lean_object* v___x_3593_; 
v_name_3592_ = lean_ctor_get(v_v_3591_, 2);
v___x_3593_ = l_Lean_TSyntax_getVersoRefName(v_name_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getName___boxed(lean_object* v_v_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_Doc_LinkRefView_getName(v_v_3594_);
lean_dec_ref(v_v_3594_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl(lean_object* v_v_3596_){
_start:
{
lean_object* v_url_3597_; lean_object* v___x_3598_; 
v_url_3597_ = lean_ctor_get(v_v_3596_, 4);
v___x_3598_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_url_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_getUrl___boxed(lean_object* v_v_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l_Lean_Doc_LinkRefView_getUrl(v_v_3599_);
lean_dec_ref(v_v_3599_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_LinkRefView_of(lean_object* v_stx_3607_){
_start:
{
lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3608_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__30));
lean_inc(v_stx_3607_);
v___x_3609_ = l_Lean_Syntax_isOfKind(v_stx_3607_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; 
lean_dec(v_stx_3607_);
v___x_3610_ = lean_box(0);
return v___x_3610_;
}
else
{
lean_object* v___x_3611_; lean_object* v_name_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3611_ = lean_unsigned_to_nat(1u);
v_name_3612_ = l_Lean_Syntax_getArg(v_stx_3607_, v___x_3611_);
v___x_3613_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_3612_);
v___x_3614_ = l_Lean_Syntax_isOfKind(v_name_3612_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; 
lean_dec(v_name_3612_);
lean_dec(v_stx_3607_);
v___x_3615_ = lean_box(0);
return v___x_3615_;
}
else
{
lean_object* v___x_3616_; lean_object* v_url_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3616_ = lean_unsigned_to_nat(3u);
v_url_3617_ = l_Lean_Syntax_getArg(v_stx_3607_, v___x_3616_);
v___x_3618_ = ((lean_object*)(l_Lean_Doc_LinkRefView_of___closed__1));
lean_inc(v_url_3617_);
v___x_3619_ = l_Lean_Syntax_isOfKind(v_url_3617_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; 
lean_dec(v_url_3617_);
lean_dec(v_name_3612_);
lean_dec(v_stx_3607_);
v___x_3620_ = lean_box(0);
return v___x_3620_;
}
else
{
lean_object* v___x_3621_; lean_object* v_opener_3622_; lean_object* v___x_3623_; lean_object* v_closer_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3621_ = lean_unsigned_to_nat(0u);
v_opener_3622_ = l_Lean_Syntax_getArg(v_stx_3607_, v___x_3621_);
v___x_3623_ = lean_unsigned_to_nat(2u);
v_closer_3624_ = l_Lean_Syntax_getArg(v_stx_3607_, v___x_3623_);
v___x_3625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3625_, 0, v_stx_3607_);
lean_ctor_set(v___x_3625_, 1, v_opener_3622_);
lean_ctor_set(v___x_3625_, 2, v_name_3612_);
lean_ctor_set(v___x_3625_, 3, v_closer_3624_);
lean_ctor_set(v___x_3625_, 4, v_url_3617_);
v___x_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3626_, 0, v___x_3625_);
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName(lean_object* v_v_3627_){
_start:
{
lean_object* v_name_3628_; lean_object* v___x_3629_; 
v_name_3628_ = lean_ctor_get(v_v_3627_, 2);
v___x_3629_ = l_Lean_TSyntax_getVersoRefName(v_name_3628_);
return v___x_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_getName___boxed(lean_object* v_v_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lean_Doc_FootnoteRefView_getName(v_v_3630_);
lean_dec_ref(v_v_3630_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_FootnoteRefView_of(lean_object* v_stx_3632_){
_start:
{
lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3633_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__29));
lean_inc(v_stx_3632_);
v___x_3634_ = l_Lean_Syntax_isOfKind(v_stx_3632_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
lean_dec(v_stx_3632_);
v___x_3635_ = lean_box(0);
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v_name_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3636_ = lean_unsigned_to_nat(1u);
v_name_3637_ = l_Lean_Syntax_getArg(v_stx_3632_, v___x_3636_);
v___x_3638_ = ((lean_object*)(l_Lean_Doc_LinkTargetView_of___closed__1));
lean_inc(v_name_3637_);
v___x_3639_ = l_Lean_Syntax_isOfKind(v_name_3637_, v___x_3638_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
lean_dec(v_name_3637_);
lean_dec(v_stx_3632_);
v___x_3640_ = lean_box(0);
return v___x_3640_;
}
else
{
lean_object* v___x_3641_; lean_object* v_opener_3642_; lean_object* v___x_3643_; lean_object* v_closer_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_content_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3641_ = lean_unsigned_to_nat(0u);
v_opener_3642_ = l_Lean_Syntax_getArg(v_stx_3632_, v___x_3641_);
v___x_3643_ = lean_unsigned_to_nat(2u);
v_closer_3644_ = l_Lean_Syntax_getArg(v_stx_3632_, v___x_3643_);
v___x_3645_ = lean_unsigned_to_nat(3u);
v___x_3646_ = l_Lean_Syntax_getArg(v_stx_3632_, v___x_3645_);
v_content_3647_ = l_Lean_Syntax_getArgs(v___x_3646_);
lean_dec(v___x_3646_);
v___x_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3648_, 0, v_stx_3632_);
lean_ctor_set(v___x_3648_, 1, v_opener_3642_);
lean_ctor_set(v___x_3648_, 2, v_name_3637_);
lean_ctor_set(v___x_3648_, 3, v_closer_3644_);
lean_ctor_set(v___x_3648_, 4, v_content_3647_);
v___x_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3648_);
return v___x_3649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(size_t v_sz_3650_, size_t v_i_3651_, lean_object* v_bs_3652_){
_start:
{
uint8_t v___x_3653_; 
v___x_3653_ = lean_usize_dec_lt(v_i_3651_, v_sz_3650_);
if (v___x_3653_ == 0)
{
return v_bs_3652_;
}
else
{
lean_object* v_v_3654_; lean_object* v___x_3655_; lean_object* v_bs_x27_3656_; size_t v___x_3657_; size_t v___x_3658_; lean_object* v___x_3659_; 
v_v_3654_ = lean_array_uget(v_bs_3652_, v_i_3651_);
v___x_3655_ = lean_unsigned_to_nat(0u);
v_bs_x27_3656_ = lean_array_uset(v_bs_3652_, v_i_3651_, v___x_3655_);
v___x_3657_ = ((size_t)1ULL);
v___x_3658_ = lean_usize_add(v_i_3651_, v___x_3657_);
v___x_3659_ = lean_array_uset(v_bs_x27_3656_, v_i_3651_, v_v_3654_);
v_i_3651_ = v___x_3658_;
v_bs_3652_ = v___x_3659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0___boxed(lean_object* v_sz_3661_, lean_object* v_i_3662_, lean_object* v_bs_3663_){
_start:
{
size_t v_sz_boxed_3664_; size_t v_i_boxed_3665_; lean_object* v_res_3666_; 
v_sz_boxed_3664_ = lean_unbox_usize(v_sz_3661_);
lean_dec(v_sz_3661_);
v_i_boxed_3665_ = lean_unbox_usize(v_i_3662_);
lean_dec(v_i_3662_);
v_res_3666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_boxed_3664_, v_i_boxed_3665_, v_bs_3663_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields(lean_object* v_v_3667_){
_start:
{
lean_object* v_contents_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; size_t v_sz_3672_; size_t v___x_3673_; lean_object* v___x_3674_; 
v_contents_3668_ = lean_ctor_get(v_v_3667_, 2);
v___x_3669_ = lean_unsigned_to_nat(0u);
v___x_3670_ = l_Lean_Syntax_getArg(v_contents_3668_, v___x_3669_);
v___x_3671_ = l_Lean_Syntax_getSepArgs(v___x_3670_);
lean_dec(v___x_3670_);
v_sz_3672_ = lean_array_size(v___x_3671_);
v___x_3673_ = ((size_t)0ULL);
v___x_3674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Doc_MetadataView_fields_spec__0(v_sz_3672_, v___x_3673_, v___x_3671_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_fields___boxed(lean_object* v_v_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Doc_MetadataView_fields(v_v_3675_);
lean_dec_ref(v_v_3675_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_MetadataView_of(lean_object* v_stx_3677_){
_start:
{
lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3678_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__28));
lean_inc(v_stx_3677_);
v___x_3679_ = l_Lean_Syntax_isOfKind(v_stx_3677_, v___x_3678_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; 
lean_dec(v_stx_3677_);
v___x_3680_ = lean_box(0);
return v___x_3680_;
}
else
{
lean_object* v___x_3681_; lean_object* v_contents_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3681_ = lean_unsigned_to_nat(1u);
v_contents_3682_ = l_Lean_Syntax_getArg(v_stx_3677_, v___x_3681_);
v___x_3683_ = ((lean_object*)(l_Lean_Doc_blockToParser___closed__26));
lean_inc(v_contents_3682_);
v___x_3684_ = l_Lean_Syntax_isOfKind(v_contents_3682_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; 
lean_dec(v_contents_3682_);
lean_dec(v_stx_3677_);
v___x_3685_ = lean_box(0);
return v___x_3685_;
}
else
{
lean_object* v___x_3686_; lean_object* v_opener_3687_; lean_object* v___x_3688_; lean_object* v_closer_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3686_ = lean_unsigned_to_nat(0u);
v_opener_3687_ = l_Lean_Syntax_getArg(v_stx_3677_, v___x_3686_);
v___x_3688_ = lean_unsigned_to_nat(2u);
v_closer_3689_ = l_Lean_Syntax_getArg(v_stx_3677_, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3690_, 0, v_stx_3677_);
lean_ctor_set(v___x_3690_, 1, v_opener_3687_);
lean_ctor_set(v___x_3690_, 2, v_contents_3682_);
lean_ctor_set(v___x_3690_, 3, v_closer_3689_);
v___x_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx(lean_object* v_x_3692_){
_start:
{
switch(lean_obj_tag(v_x_3692_))
{
case 0:
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_unsigned_to_nat(0u);
return v___x_3693_;
}
case 1:
{
lean_object* v___x_3694_; 
v___x_3694_ = lean_unsigned_to_nat(1u);
return v___x_3694_;
}
case 2:
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_unsigned_to_nat(2u);
return v___x_3695_;
}
case 3:
{
lean_object* v___x_3696_; 
v___x_3696_ = lean_unsigned_to_nat(3u);
return v___x_3696_;
}
case 4:
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_unsigned_to_nat(4u);
return v___x_3697_;
}
case 5:
{
lean_object* v___x_3698_; 
v___x_3698_ = lean_unsigned_to_nat(5u);
return v___x_3698_;
}
case 6:
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_unsigned_to_nat(6u);
return v___x_3699_;
}
case 7:
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_unsigned_to_nat(7u);
return v___x_3700_;
}
case 8:
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_unsigned_to_nat(8u);
return v___x_3701_;
}
case 9:
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_unsigned_to_nat(9u);
return v___x_3702_;
}
case 10:
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_unsigned_to_nat(10u);
return v___x_3703_;
}
default: 
{
lean_object* v___x_3704_; 
v___x_3704_ = lean_unsigned_to_nat(11u);
return v___x_3704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorIdx___boxed(lean_object* v_x_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Doc_BlockView_ctorIdx(v_x_3705_);
lean_dec_ref(v_x_3705_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___redArg(lean_object* v_t_3707_, lean_object* v_k_3708_){
_start:
{
lean_object* v_view_3709_; lean_object* v___x_3710_; 
v_view_3709_ = lean_ctor_get(v_t_3707_, 0);
lean_inc_ref(v_view_3709_);
lean_dec_ref(v_t_3707_);
v___x_3710_ = lean_apply_1(v_k_3708_, v_view_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim(lean_object* v_motive_3711_, lean_object* v_ctorIdx_3712_, lean_object* v_t_3713_, lean_object* v_h_3714_, lean_object* v_k_3715_){
_start:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3713_, v_k_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ctorElim___boxed(lean_object* v_motive_3717_, lean_object* v_ctorIdx_3718_, lean_object* v_t_3719_, lean_object* v_h_3720_, lean_object* v_k_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Doc_BlockView_ctorElim(v_motive_3717_, v_ctorIdx_3718_, v_t_3719_, v_h_3720_, v_k_3721_);
lean_dec(v_ctorIdx_3718_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim___redArg(lean_object* v_t_3723_, lean_object* v_para_3724_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3723_, v_para_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_para_elim(lean_object* v_motive_3726_, lean_object* v_t_3727_, lean_object* v_h_3728_, lean_object* v_para_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3727_, v_para_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim___redArg(lean_object* v_t_3731_, lean_object* v_ul_3732_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3731_, v_ul_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ul_elim(lean_object* v_motive_3734_, lean_object* v_t_3735_, lean_object* v_h_3736_, lean_object* v_ul_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3735_, v_ul_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim___redArg(lean_object* v_t_3739_, lean_object* v_ol_3740_){
_start:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3739_, v_ol_3740_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_ol_elim(lean_object* v_motive_3742_, lean_object* v_t_3743_, lean_object* v_h_3744_, lean_object* v_ol_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3743_, v_ol_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim___redArg(lean_object* v_t_3747_, lean_object* v_dl_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3747_, v_dl_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_dl_elim(lean_object* v_motive_3750_, lean_object* v_t_3751_, lean_object* v_h_3752_, lean_object* v_dl_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3751_, v_dl_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim___redArg(lean_object* v_t_3755_, lean_object* v_blockquote_3756_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3755_, v_blockquote_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_blockquote_elim(lean_object* v_motive_3758_, lean_object* v_t_3759_, lean_object* v_h_3760_, lean_object* v_blockquote_3761_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3759_, v_blockquote_3761_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim___redArg(lean_object* v_t_3763_, lean_object* v_codeblock_3764_){
_start:
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3763_, v_codeblock_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_codeblock_elim(lean_object* v_motive_3766_, lean_object* v_t_3767_, lean_object* v_h_3768_, lean_object* v_codeblock_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3767_, v_codeblock_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim___redArg(lean_object* v_t_3771_, lean_object* v_directive_3772_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3771_, v_directive_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_directive_elim(lean_object* v_motive_3774_, lean_object* v_t_3775_, lean_object* v_h_3776_, lean_object* v_directive_3777_){
_start:
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3775_, v_directive_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim___redArg(lean_object* v_t_3779_, lean_object* v_command_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3779_, v_command_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_command_elim(lean_object* v_motive_3782_, lean_object* v_t_3783_, lean_object* v_h_3784_, lean_object* v_command_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3783_, v_command_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim___redArg(lean_object* v_t_3787_, lean_object* v_header_3788_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3787_, v_header_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_header_elim(lean_object* v_motive_3790_, lean_object* v_t_3791_, lean_object* v_h_3792_, lean_object* v_header_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3791_, v_header_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim___redArg(lean_object* v_t_3795_, lean_object* v_linkRef_3796_){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3795_, v_linkRef_3796_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_linkRef_elim(lean_object* v_motive_3798_, lean_object* v_t_3799_, lean_object* v_h_3800_, lean_object* v_linkRef_3801_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3799_, v_linkRef_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim___redArg(lean_object* v_t_3803_, lean_object* v_footnoteRef_3804_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3803_, v_footnoteRef_3804_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_footnoteRef_elim(lean_object* v_motive_3806_, lean_object* v_t_3807_, lean_object* v_h_3808_, lean_object* v_footnoteRef_3809_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3807_, v_footnoteRef_3809_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim___redArg(lean_object* v_t_3811_, lean_object* v_metadata_3812_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3811_, v_metadata_3812_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_metadata_elim(lean_object* v_motive_3814_, lean_object* v_t_3815_, lean_object* v_h_3816_, lean_object* v_metadata_3817_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_Doc_BlockView_ctorElim___redArg(v_t_3815_, v_metadata_3817_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeParaViewBlockView___lam__0(lean_object* v_view_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3820_, 0, v_view_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeUnorderedListViewBlockView___lam__0(lean_object* v_view_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_view_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeOrderedListViewBlockView___lam__0(lean_object* v_view_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_view_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDescListViewBlockView___lam__0(lean_object* v_view_3831_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3832_, 0, v_view_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeBlockquoteViewBlockView___lam__0(lean_object* v_view_3835_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_view_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCodeBlockViewBlockView___lam__0(lean_object* v_view_3839_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3840_, 0, v_view_3839_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeDirectiveViewBlockView___lam__0(lean_object* v_view_3843_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3844_, 0, v_view_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeCommandViewBlockView___lam__0(lean_object* v_view_3847_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3848_, 0, v_view_3847_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeHeaderViewBlockView___lam__0(lean_object* v_view_3851_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3852_, 0, v_view_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeLinkRefViewBlockView___lam__0(lean_object* v_view_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3856_, 0, v_view_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeFootnoteRefViewBlockView___lam__0(lean_object* v_view_3859_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3860_, 0, v_view_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeMetadataViewBlockView___lam__0(lean_object* v_view_3863_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3864_, 0, v_view_3863_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx(lean_object* v_x_3867_){
_start:
{
lean_object* v_view_3868_; lean_object* v_stx_3869_; 
v_view_3868_ = lean_ctor_get(v_x_3867_, 0);
v_stx_3869_ = lean_ctor_get(v_view_3868_, 0);
lean_inc(v_stx_3869_);
return v_stx_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_stx___boxed(lean_object* v_x_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_Doc_BlockView_stx(v_x_3870_);
lean_dec_ref(v_x_3870_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_BlockView_of(lean_object* v_stx_3872_){
_start:
{
lean_object* v___x_3873_; 
lean_inc(v_stx_3872_);
v___x_3873_ = l_Lean_Doc_ParaView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v___x_3874_; 
lean_inc(v_stx_3872_);
v___x_3874_ = l_Lean_Doc_UnorderedListView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v___x_3875_; 
lean_inc(v_stx_3872_);
v___x_3875_ = l_Lean_Doc_OrderedListView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v___x_3876_; 
lean_inc(v_stx_3872_);
v___x_3876_ = l_Lean_Doc_DescListView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v___x_3877_; 
lean_inc(v_stx_3872_);
v___x_3877_ = l_Lean_Doc_BlockquoteView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v___x_3878_; 
lean_inc(v_stx_3872_);
v___x_3878_ = l_Lean_Doc_CodeBlockView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v___x_3879_; 
lean_inc(v_stx_3872_);
v___x_3879_ = l_Lean_Doc_DirectiveView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v___x_3880_; 
lean_inc(v_stx_3872_);
v___x_3880_ = l_Lean_Doc_CommandView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; 
lean_inc(v_stx_3872_);
v___x_3881_ = l_Lean_Doc_HeaderView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v___x_3882_; 
lean_inc(v_stx_3872_);
v___x_3882_ = l_Lean_Doc_LinkRefView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v___x_3883_; 
lean_inc(v_stx_3872_);
v___x_3883_ = l_Lean_Doc_FootnoteRefView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_Doc_MetadataView_of(v_stx_3872_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_box(0);
return v___x_3885_;
}
else
{
lean_object* v_val_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3894_; 
v_val_3886_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3888_ = v___x_3884_;
v_isShared_3889_ = v_isSharedCheck_3894_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_val_3886_);
lean_dec(v___x_3884_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3894_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; lean_object* v___x_3892_; 
v___x_3890_ = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(v___x_3890_, 0, v_val_3886_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3890_);
v___x_3892_ = v___x_3888_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3890_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
else
{
lean_object* v_val_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3903_; 
lean_dec(v_stx_3872_);
v_val_3895_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3897_ = v___x_3883_;
v_isShared_3898_ = v_isSharedCheck_3903_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_val_3895_);
lean_dec(v___x_3883_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3903_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3899_; lean_object* v___x_3901_; 
v___x_3899_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3899_, 0, v_val_3895_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3899_);
v___x_3901_ = v___x_3897_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
else
{
lean_object* v_val_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v_stx_3872_);
v_val_3904_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3906_ = v___x_3882_;
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_val_3904_);
lean_dec(v___x_3882_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3912_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
v___x_3908_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_3908_, 0, v_val_3904_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3908_);
v___x_3910_ = v___x_3906_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v_val_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_stx_3872_);
v_val_3913_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3915_ = v___x_3881_;
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_val_3913_);
lean_dec(v___x_3881_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3921_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_3917_, 0, v_val_3913_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3917_);
v___x_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v_val_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_stx_3872_);
v_val_3922_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3924_ = v___x_3880_;
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_val_3922_);
lean_dec(v___x_3880_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3930_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3926_, 0, v_val_3922_);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v___x_3926_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_val_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v_stx_3872_);
v_val_3931_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3933_ = v___x_3879_;
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_val_3931_);
lean_dec(v___x_3879_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3939_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3935_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_3935_, 0, v_val_3931_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3935_);
v___x_3937_ = v___x_3933_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_object* v_val_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3948_; 
lean_dec(v_stx_3872_);
v_val_3940_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3942_ = v___x_3878_;
v_isShared_3943_ = v_isSharedCheck_3948_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_val_3940_);
lean_dec(v___x_3878_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3948_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3944_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_3944_, 0, v_val_3940_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3944_);
v___x_3946_ = v___x_3942_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v_val_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3957_; 
lean_dec(v_stx_3872_);
v_val_3949_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3951_ = v___x_3877_;
v_isShared_3952_ = v_isSharedCheck_3957_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_val_3949_);
lean_dec(v___x_3877_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3957_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_val_3949_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 0, v___x_3953_);
v___x_3955_ = v___x_3951_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
else
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3966_; 
lean_dec(v_stx_3872_);
v_val_3958_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3960_ = v___x_3876_;
v_isShared_3961_ = v_isSharedCheck_3966_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v___x_3876_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3966_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
v___x_3962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3962_, 0, v_val_3958_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3962_);
v___x_3964_ = v___x_3960_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
else
{
lean_object* v_val_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3975_; 
lean_dec(v_stx_3872_);
v_val_3967_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3969_ = v___x_3875_;
v_isShared_3970_ = v_isSharedCheck_3975_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_val_3967_);
lean_dec(v___x_3875_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3975_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3971_; lean_object* v___x_3973_; 
v___x_3971_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3971_, 0, v_val_3967_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3971_);
v___x_3973_ = v___x_3969_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
else
{
lean_object* v_val_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3984_; 
lean_dec(v_stx_3872_);
v_val_3976_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3978_ = v___x_3874_;
v_isShared_3979_ = v_isSharedCheck_3984_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_val_3976_);
lean_dec(v___x_3874_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3984_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3980_, 0, v_val_3976_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_3980_);
v___x_3982_ = v___x_3978_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
else
{
lean_object* v_val_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3993_; 
lean_dec(v_stx_3872_);
v_val_3985_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3987_ = v___x_3873_;
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_val_3985_);
lean_dec(v___x_3873_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3993_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v_val_3985_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_View(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__0___boxed__const__1);
l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__1___boxed__const__1);
l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1 = _init_l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_UnorderedListItemView_of___closed__2___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_View(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_View(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_View(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_View(builtin);
}
#ifdef __cplusplus
}
#endif

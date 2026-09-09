// Lean compiler output
// Module: Lean.Fmt.FmtM.CommonFormatters
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Term import Init.Data import Init.While
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object*);
uint8_t l_Lean_Fmt_propagatesRhsStickiness(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtProjLike___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtProjLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtProjLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__0 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__0_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__1 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__1_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__2 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__2_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__3 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__3_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__4 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__4_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__5 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__6_value_aux_0),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__6_value_aux_1),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__6_value_aux_2),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__5_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__6 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__6_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "namedArgument"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__7 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__8_value_aux_0),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__8_value_aux_1),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__8_value_aux_2),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__7_value),LEAN_SCALAR_PTR_LITERAL(226, 89, 129, 113, 173, 121, 169, 188)}};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__8 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__8_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__9 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__10 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__10_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__11 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__12_value_aux_0),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__12_value_aux_1),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__12_value_aux_2),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__11_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__12 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__12_value;
static const lean_string_object l_Lean_Fmt_allowAppArgFill___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__13 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__13_value;
static const lean_ctor_object l_Lean_Fmt_allowAppArgFill___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__13_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Fmt_allowAppArgFill___closed__14 = (const lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__14_value;
LEAN_EXPORT uint8_t l_Lean_Fmt_allowAppArgFill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_allowAppArgFill___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0___redArg(lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_fmtAppLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtAppLike___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAppLike___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtAppLike___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_Lean_Fmt_fmtAppLike___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAppLike___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtAppLike___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAppLike___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAppLike___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtAppLike___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAppLike___closed__2_value_aux_1),((lean_object*)&l_Lean_Fmt_allowAppArgFill___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtAppLike___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAppLike___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAppLike___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_Lean_Fmt_fmtAppLike___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtAppLike___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAppLike___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtProjLike___lam__0(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_lhs_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; lean_object* v___x_11_; 
v___x_4_ = lean_unsigned_to_nat(3u);
v___x_5_ = lean_mk_empty_array_with_capacity(v___x_4_);
v___x_6_ = lean_array_push(v___x_5_, v_lhs_3_);
v___x_7_ = lean_array_push(v___x_6_, v_a_1_);
v___x_8_ = lean_array_push(v___x_7_, v_a_2_);
v___x_9_ = l_Lean_Fmt_Layouts_atomic(v___x_8_);
lean_dec_ref(v___x_8_);
v___x_10_ = 0;
v___x_11_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_9_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtProjLike(lean_object* v_lhs_12_, lean_object* v_dotTk_13_, lean_object* v_field_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Fmt_fmt(v_dotTk_13_, v_a_15_, v_a_16_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v___x_17_, 1);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_17_, 2);
v___x_20_ = l_Lean_Fmt_fmt(v_field_14_, v_a_15_, v_a_19_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_32_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_a_22_ = lean_ctor_get(v___x_20_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_32_ == 0)
{
v___x_24_ = v___x_20_;
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_32_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___f_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___f_26_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtProjLike___lam__0), 3, 2);
lean_closure_set(v___f_26_, 0, v_a_18_);
lean_closure_set(v___f_26_, 1, v_a_21_);
v___x_27_ = lean_box(0);
v___x_28_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_lhs_12_, v___f_26_, v___x_27_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_28_);
v___x_30_ = v___x_24_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_a_22_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
else
{
lean_dec(v_a_18_);
lean_dec_ref(v_lhs_12_);
return v___x_20_;
}
}
else
{
lean_dec(v_field_14_);
lean_dec_ref(v_lhs_12_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtProjLike___boxed(lean_object* v_lhs_33_, lean_object* v_dotTk_34_, lean_object* v_field_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Fmt_fmtProjLike(v_lhs_33_, v_dotTk_34_, v_field_35_, v_a_36_, v_a_37_);
lean_dec_ref(v_a_36_);
return v_res_38_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_allowAppArgFill(lean_object* v_x_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__4));
lean_inc(v_x_72_);
v___x_74_ = l_Lean_Syntax_isOfKind(v_x_72_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; uint8_t v___x_76_; uint8_t v___x_77_; 
v___x_75_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__6));
lean_inc(v_x_72_);
v___x_76_ = l_Lean_Syntax_isOfKind(v_x_72_, v___x_75_);
v___x_77_ = 1;
if (v___x_76_ == 0)
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__8));
lean_inc(v_x_72_);
v___x_83_ = l_Lean_Syntax_isOfKind(v_x_72_, v___x_82_);
if (v___x_83_ == 0)
{
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
if (v___x_76_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = l_Lean_Syntax_getArg(v_x_72_, v___x_84_);
v___x_86_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__10));
v___x_87_ = l_Lean_Syntax_isOfKind(v___x_85_, v___x_86_);
if (v___x_87_ == 0)
{
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
goto v___jp_78_;
}
}
else
{
goto v___jp_78_;
}
}
}
else
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = l_Lean_Syntax_getArg(v_x_72_, v___x_88_);
v___x_90_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__12));
lean_inc(v___x_89_);
v___x_91_ = l_Lean_Syntax_isOfKind(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
lean_dec(v___x_89_);
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v___x_93_ = l_Lean_Syntax_getArg(v___x_89_, v___x_92_);
lean_dec(v___x_89_);
v___x_94_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__14));
lean_inc(v___x_93_);
v___x_95_ = l_Lean_Syntax_isOfKind(v___x_93_, v___x_94_);
if (v___x_95_ == 0)
{
lean_dec(v___x_93_);
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_96_ = l_Lean_Syntax_getArg(v___x_93_, v___x_88_);
lean_dec(v___x_93_);
v___x_97_ = lean_box(0);
v___x_98_ = l_Lean_Syntax_matchesIdent(v___x_96_, v___x_97_);
lean_dec(v___x_96_);
if (v___x_98_ == 0)
{
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = l_Lean_Syntax_getArg(v_x_72_, v___x_92_);
lean_dec(v_x_72_);
v___x_100_ = l_Lean_Syntax_isOfKind(v___x_99_, v___x_73_);
if (v___x_100_ == 0)
{
return v___x_77_;
}
else
{
return v___x_74_;
}
}
}
}
}
v___jp_78_:
{
if (v___x_76_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(3u);
v___x_80_ = l_Lean_Syntax_getArg(v_x_72_, v___x_79_);
lean_dec(v_x_72_);
v___x_81_ = l_Lean_Syntax_isOfKind(v___x_80_, v___x_73_);
if (v___x_81_ == 0)
{
return v___x_77_;
}
else
{
return v___x_76_;
}
}
else
{
lean_dec(v_x_72_);
return v___x_76_;
}
}
}
else
{
uint8_t v___x_101_; 
lean_dec(v_x_72_);
v___x_101_ = 0;
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_allowAppArgFill___boxed(lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_Fmt_allowAppArgFill(v_x_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0(size_t v_sz_105_, size_t v_i_106_, lean_object* v_bs_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_usize_dec_lt(v_i_106_, v_sz_105_);
if (v___x_108_ == 0)
{
return v_bs_107_;
}
else
{
lean_object* v_v_109_; lean_object* v_v_110_; lean_object* v___x_111_; lean_object* v_bs_x27_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; 
v_v_109_ = lean_array_uget_borrowed(v_bs_107_, v_i_106_);
v_v_110_ = lean_ctor_get(v_v_109_, 0);
lean_inc(v_v_110_);
v___x_111_ = lean_unsigned_to_nat(0u);
v_bs_x27_112_ = lean_array_uset(v_bs_107_, v_i_106_, v___x_111_);
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_add(v_i_106_, v___x_113_);
v___x_115_ = lean_array_uset(v_bs_x27_112_, v_i_106_, v_v_110_);
v_i_106_ = v___x_114_;
v_bs_107_ = v___x_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0___boxed(lean_object* v_sz_117_, lean_object* v_i_118_, lean_object* v_bs_119_){
_start:
{
size_t v_sz_boxed_120_; size_t v_i_boxed_121_; lean_object* v_res_122_; 
v_sz_boxed_120_ = lean_unbox_usize(v_sz_117_);
lean_dec(v_sz_117_);
v_i_boxed_121_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0(v_sz_boxed_120_, v_i_boxed_121_, v_bs_119_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1(size_t v_sz_123_, size_t v_i_124_, lean_object* v_bs_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_lt(v_i_124_, v_sz_123_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_bs_125_);
lean_ctor_set(v___x_129_, 1, v___y_127_);
return v___x_129_;
}
else
{
lean_object* v_v_130_; lean_object* v___x_131_; 
v_v_130_ = lean_array_uget(v_bs_125_, v_i_124_);
lean_inc(v_v_130_);
v___x_131_ = l_Lean_Fmt_fmt(v_v_130_, v___y_126_, v___y_127_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v_a_133_; lean_object* v___x_134_; lean_object* v_bs_x27_135_; uint8_t v___x_136_; lean_object* v___x_137_; size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
v_a_133_ = lean_ctor_get(v___x_131_, 1);
lean_inc(v_a_133_);
lean_dec_ref_known(v___x_131_, 2);
v___x_134_ = lean_unsigned_to_nat(0u);
v_bs_x27_135_ = lean_array_uset(v_bs_125_, v_i_124_, v___x_134_);
v___x_136_ = l_Lean_Fmt_allowAppArgFill(v_v_130_);
v___x_137_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_137_, 0, v_a_132_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*1, v___x_136_);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_add(v_i_124_, v___x_138_);
v___x_140_ = lean_array_uset(v_bs_x27_135_, v_i_124_, v___x_137_);
v_i_124_ = v___x_139_;
v_bs_125_ = v___x_140_;
v___y_127_ = v_a_133_;
goto _start;
}
else
{
lean_object* v_a_142_; lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
lean_dec(v_v_130_);
lean_dec_ref(v_bs_125_);
v_a_142_ = lean_ctor_get(v___x_131_, 0);
v_a_143_ = lean_ctor_get(v___x_131_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_131_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_inc(v_a_142_);
lean_dec(v___x_131_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_142_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1___boxed(lean_object* v_sz_151_, lean_object* v_i_152_, lean_object* v_bs_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v_sz_boxed_156_ = lean_unbox_usize(v_sz_151_);
lean_dec(v_sz_151_);
v_i_boxed_157_ = lean_unbox_usize(v_i_152_);
lean_dec(v_i_152_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1(v_sz_boxed_156_, v_i_boxed_157_, v_bs_153_, v___y_154_, v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_158_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2(lean_object* v_as_159_, size_t v_i_160_, size_t v_stop_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = lean_usize_dec_eq(v_i_160_, v_stop_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v_allowFill_164_; 
v___x_163_ = lean_array_uget_borrowed(v_as_159_, v_i_160_);
v_allowFill_164_ = lean_ctor_get_uint8(v___x_163_, sizeof(void*)*1);
if (v_allowFill_164_ == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 1;
return v___x_165_;
}
else
{
size_t v___x_166_; size_t v___x_167_; 
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_i_160_, v___x_166_);
v_i_160_ = v___x_167_;
goto _start;
}
}
else
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2___boxed(lean_object* v_as_170_, lean_object* v_i_171_, lean_object* v_stop_172_){
_start:
{
size_t v_i_boxed_173_; size_t v_stop_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v_i_boxed_173_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_stop_boxed_174_ = lean_unbox_usize(v_stop_172_);
lean_dec(v_stop_172_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2(v_as_170_, v_i_boxed_173_, v_stop_boxed_174_);
lean_dec_ref(v_as_170_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp_x27(lean_object* v_f_177_, lean_object* v_args_178_, lean_object* v_format_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_args_183_; lean_object* v___y_184_; size_t v_sz_197_; size_t v___x_198_; lean_object* v___x_199_; 
v_sz_197_ = lean_array_size(v_args_178_);
v___x_198_ = ((size_t)0ULL);
v___x_199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1(v_sz_197_, v___x_198_, v_args_178_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v_a_200_; lean_object* v_a_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_220_; lean_object* v_array_221_; lean_object* v_start_222_; lean_object* v_stop_223_; lean_object* v___y_225_; uint8_t v___x_230_; 
v_a_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc_n(v_a_200_, 2);
v_a_201_ = lean_ctor_get(v___x_199_, 1);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_199_, 2);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_array_get_size(v_a_200_);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_sub(v___x_203_, v___x_204_);
lean_inc(v___x_205_);
v___x_220_ = l_Array_toSubarray___redArg(v_a_200_, v___x_202_, v___x_205_);
v_array_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_ref(v_array_221_);
v_start_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_start_222_);
v_stop_223_ = lean_ctor_get(v___x_220_, 2);
lean_inc(v_stop_223_);
lean_dec_ref(v___x_220_);
v___x_230_ = lean_nat_dec_lt(v_start_222_, v_stop_223_);
if (v___x_230_ == 0)
{
lean_dec(v_stop_223_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
goto v___jp_206_;
}
else
{
lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_array_get_size(v_array_221_);
v___x_232_ = lean_nat_dec_le(v_stop_223_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v_stop_223_);
v___y_225_ = v___x_231_;
goto v___jp_224_;
}
else
{
v___y_225_ = v_stop_223_;
goto v___jp_224_;
}
}
v___jp_206_:
{
uint8_t v___x_207_; 
v___x_207_ = lean_nat_dec_lt(v___x_205_, v___x_203_);
if (v___x_207_ == 0)
{
lean_dec(v___x_205_);
v_args_183_ = v_a_200_;
v___y_184_ = v_a_201_;
goto v___jp_182_;
}
else
{
lean_object* v_v_208_; lean_object* v_v_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_219_; 
v_v_208_ = lean_array_fget(v_a_200_, v___x_205_);
v_v_209_ = lean_ctor_get(v_v_208_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_v_208_);
if (v_isSharedCheck_219_ == 0)
{
v___x_211_ = v_v_208_;
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_v_209_);
lean_dec(v_v_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_219_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v_xs_x27_214_; lean_object* v___x_216_; 
v___x_213_ = lean_box(0);
v_xs_x27_214_ = lean_array_fset(v_a_200_, v___x_205_, v___x_213_);
if (v_isShared_212_ == 0)
{
v___x_216_ = v___x_211_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_v_209_);
v___x_216_ = v_reuseFailAlloc_218_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*1, v___x_207_);
v___x_217_ = lean_array_fset(v_xs_x27_214_, v___x_205_, v___x_216_);
lean_dec(v___x_205_);
v_args_183_ = v___x_217_;
v___y_184_ = v_a_201_;
goto v___jp_182_;
}
}
}
}
v___jp_224_:
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_lt(v_start_222_, v___y_225_);
if (v___x_226_ == 0)
{
lean_dec(v___y_225_);
lean_dec(v_start_222_);
lean_dec_ref(v_array_221_);
goto v___jp_206_;
}
else
{
size_t v___x_227_; size_t v___x_228_; uint8_t v___x_229_; 
v___x_227_ = lean_usize_of_nat(v_start_222_);
lean_dec(v_start_222_);
v___x_228_ = lean_usize_of_nat(v___y_225_);
lean_dec(v___y_225_);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2(v_array_221_, v___x_227_, v___x_228_);
lean_dec_ref(v_array_221_);
if (v___x_229_ == 0)
{
goto v___jp_206_;
}
else
{
lean_dec(v___x_205_);
v_args_183_ = v_a_200_;
v___y_184_ = v_a_201_;
goto v___jp_182_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_f_177_);
v_a_233_ = lean_ctor_get(v___x_199_, 0);
v_a_234_ = lean_ctor_get(v___x_199_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_199_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_inc(v_a_233_);
lean_dec(v___x_199_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_233_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
v___jp_182_:
{
uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; size_t v_sz_192_; size_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_185_ = 1;
v___x_186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_186_, 0, v_f_177_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_mk_empty_array_with_capacity(v___x_187_);
v___x_189_ = lean_array_push(v___x_188_, v___x_186_);
v___x_190_ = l_Array_append___redArg(v___x_189_, v_args_183_);
v___x_191_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_190_, v_format_179_);
lean_dec_ref(v___x_190_);
v_sz_192_ = lean_array_size(v_args_183_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0(v_sz_192_, v___x_193_, v_args_183_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_191_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___y_184_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp_x27___boxed(lean_object* v_f_242_, lean_object* v_args_243_, lean_object* v_format_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Fmt_fmtFixedApp_x27(v_f_242_, v_args_243_, v_format_244_, v_a_245_, v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec_ref(v_format_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp(lean_object* v_f_248_, lean_object* v_args_249_, lean_object* v_format_250_, lean_object* v_a_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Fmt_fmtFixedApp_x27(v_f_248_, v_args_249_, v_format_250_, v_a_251_, v_a_252_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_a_255_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_253_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_fst_259_; lean_object* v___x_261_; 
v_fst_259_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_fst_259_);
lean_dec(v_a_254_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v_fst_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_fst_259_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v_a_255_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_264_ = lean_ctor_get(v___x_253_, 0);
v_a_265_ = lean_ctor_get(v___x_253_, 1);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_253_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_inc(v_a_264_);
lean_dec(v___x_253_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_264_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp___boxed(lean_object* v_f_273_, lean_object* v_args_274_, lean_object* v_format_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Fmt_fmtFixedApp(v_f_273_, v_args_274_, v_format_275_, v_a_276_, v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec_ref(v_format_275_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0___redArg(lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
lean_object* v_array_281_; lean_object* v_start_282_; lean_object* v_stop_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_296_; 
v_array_281_ = lean_ctor_get(v_a_279_, 0);
v_start_282_ = lean_ctor_get(v_a_279_, 1);
v_stop_283_ = lean_ctor_get(v_a_279_, 2);
v_isSharedCheck_296_ = !lean_is_exclusive(v_a_279_);
if (v_isSharedCheck_296_ == 0)
{
v___x_285_ = v_a_279_;
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_stop_283_);
lean_inc(v_start_282_);
lean_inc(v_array_281_);
lean_dec(v_a_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_296_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
uint8_t v___x_287_; 
v___x_287_ = lean_nat_dec_lt(v_start_282_, v_stop_283_);
if (v___x_287_ == 0)
{
lean_del_object(v___x_285_);
lean_dec(v_stop_283_);
lean_dec(v_start_282_);
lean_dec_ref(v_array_281_);
return v_b_280_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_start_282_, v___x_288_);
lean_inc_ref(v_array_281_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_289_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_array_281_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_stop_283_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_array_fget(v_array_281_, v_start_282_);
lean_dec(v_start_282_);
lean_dec_ref(v_array_281_);
v___x_293_ = lean_array_push(v_b_280_, v___x_292_);
v_a_279_ = v___x_291_;
v_b_280_ = v___x_293_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAppLike(lean_object* v_terms_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_array_get_size(v_terms_305_);
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_nat_dec_eq(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v_fStx_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_args_318_; lean_object* v_fst_320_; lean_object* v_snd_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_311_ = lean_box(0);
v___x_312_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_313_ = 1;
v_fStx_314_ = lean_array_get(v___x_311_, v_terms_305_, v___x_309_);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = l_Array_toSubarray___redArg(v_terms_305_, v___x_315_, v___x_308_);
v___x_317_ = ((lean_object*)(l_Lean_Fmt_fmtAppLike___closed__0));
v_args_318_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0___redArg(v___x_316_, v___x_317_);
v___x_363_ = ((lean_object*)(l_Lean_Fmt_fmtAppLike___closed__2));
lean_inc(v_fStx_314_);
v___x_364_ = l_Lean_Syntax_isOfKind(v_fStx_314_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
lean_inc(v_fStx_314_);
v___x_365_ = l_Lean_Fmt_fmt(v_fStx_314_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v_a_367_; lean_object* v___x_368_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
v_a_367_ = lean_ctor_get(v___x_365_, 1);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_365_, 2);
v___x_368_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_368_, 0, v___x_313_);
lean_ctor_set_uint8(v___x_368_, 1, v___x_364_);
lean_ctor_set_uint8(v___x_368_, 2, v___x_313_);
lean_ctor_set_uint8(v___x_368_, 3, v___x_313_);
v_fst_320_ = v_a_366_;
v_snd_321_ = v___x_368_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_367_;
goto v___jp_319_;
}
else
{
lean_dec_ref(v_args_318_);
lean_dec(v_fStx_314_);
return v___x_365_;
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = l_Lean_Syntax_getArg(v_fStx_314_, v___x_309_);
v___x_370_ = l_Lean_Fmt_fmt(v___x_369_, v_a_306_, v_a_307_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v_a_372_; lean_object* v_dotTk_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc_n(v_a_371_, 2);
v_a_372_ = lean_ctor_get(v___x_370_, 1);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_370_, 2);
v_dotTk_373_ = l_Lean_Syntax_getArg(v_fStx_314_, v___x_315_);
v___x_374_ = lean_unsigned_to_nat(2u);
v___x_375_ = l_Lean_Syntax_getArg(v_fStx_314_, v___x_374_);
v___x_376_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_a_371_);
v___x_377_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_377_, 0, v___x_313_);
lean_ctor_set_uint8(v___x_377_, 1, v___x_376_);
lean_ctor_set_uint8(v___x_377_, 2, v___x_313_);
lean_ctor_set_uint8(v___x_377_, 3, v___x_313_);
v___x_378_ = l_Lean_Fmt_fmtProjLike(v_a_371_, v_dotTk_373_, v___x_375_, v_a_306_, v_a_372_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v_a_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
v_a_380_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_378_, 2);
v_fst_320_ = v_a_379_;
v_snd_321_ = v___x_377_;
v___y_322_ = v_a_306_;
v___y_323_ = v_a_380_;
goto v___jp_319_;
}
else
{
lean_dec_ref_known(v___x_377_, 0);
lean_dec_ref(v_args_318_);
lean_dec(v_fStx_314_);
return v___x_378_;
}
}
else
{
lean_dec_ref(v_args_318_);
lean_dec(v_fStx_314_);
return v___x_370_;
}
}
v___jp_319_:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Fmt_fmtFixedApp_x27(v_fst_320_, v_args_318_, v_snd_321_, v___y_322_, v___y_323_);
lean_dec_ref(v_snd_321_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_353_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_a_326_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_353_ == 0)
{
v___x_328_ = v___x_324_;
v_isShared_329_ = v_isSharedCheck_353_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_353_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v_fst_330_; lean_object* v_snd_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_fst_330_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_fst_330_);
v_snd_331_ = lean_ctor_get(v_a_325_, 1);
lean_inc(v_snd_331_);
lean_dec(v_a_325_);
v___x_332_ = lean_array_get_size(v_snd_331_);
v___x_333_ = lean_nat_dec_eq(v___x_332_, v___x_315_);
if (v___x_333_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_snd_331_);
lean_dec(v_fStx_314_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v_fst_330_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_a_326_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_array_get(v___x_312_, v_snd_331_, v___x_309_);
lean_dec(v_snd_331_);
v___x_338_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_337_);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_object* v_val_339_; lean_object* v_env_340_; uint8_t v___x_341_; 
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v___x_338_, 1);
v_env_340_ = lean_ctor_get(v___y_322_, 0);
lean_inc_ref(v_env_340_);
v___x_341_ = l_Lean_Fmt_propagatesRhsStickiness(v_env_340_, v_fStx_314_);
if (v___x_341_ == 0)
{
lean_object* v___x_343_; 
lean_dec(v_val_339_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v_fst_330_);
v___x_343_ = v___x_328_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_a_326_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
uint8_t v_kind_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v_kind_345_ = lean_ctor_get_uint8(v_val_339_, sizeof(void*)*1);
lean_dec(v_val_339_);
lean_inc(v_fst_330_);
v___x_346_ = l_Lean_Fmt_TaggedDoc_sticky(v_fst_330_, v_fst_330_, v_kind_345_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_346_);
v___x_348_ = v___x_328_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_a_326_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v___x_351_; 
lean_dec(v___x_338_);
lean_dec(v_fStx_314_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v_fst_330_);
v___x_351_ = v___x_328_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_a_326_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_fStx_314_);
v_a_354_ = lean_ctor_get(v___x_324_, 0);
v_a_355_ = lean_ctor_get(v___x_324_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_324_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_inc(v_a_354_);
lean_dec(v___x_324_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_354_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec_ref(v_terms_305_);
v___x_381_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_307_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAppLike___boxed(lean_object* v_terms_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Fmt_fmtAppLike(v_terms_383_, v_a_384_, v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0(lean_object* v_inst_387_, lean_object* v_R_388_, lean_object* v_a_389_, lean_object* v_b_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0___redArg(v_a_389_, v_b_390_);
return v___x_391_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
}
#ifdef __cplusplus
}
#endif

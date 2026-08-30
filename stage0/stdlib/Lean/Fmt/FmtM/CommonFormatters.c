// Lean compiler output
// Module: Lean.Fmt.FmtM.CommonFormatters
// Imports: public import Lean.Fmt.FmtM.Basic import Init.Data import Init.While
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
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
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
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__8));
lean_inc(v_x_72_);
v___x_79_ = l_Lean_Syntax_isOfKind(v_x_72_, v___x_78_);
if (v___x_79_ == 0)
{
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_72_, v___x_80_);
v___x_82_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__10));
v___x_83_ = l_Lean_Syntax_isOfKind(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = lean_unsigned_to_nat(3u);
v___x_85_ = l_Lean_Syntax_getArg(v_x_72_, v___x_84_);
lean_dec(v_x_72_);
v___x_86_ = l_Lean_Syntax_isOfKind(v___x_85_, v___x_73_);
if (v___x_86_ == 0)
{
return v___x_77_;
}
else
{
return v___x_76_;
}
}
}
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_Lean_Syntax_getArg(v_x_72_, v___x_87_);
v___x_89_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__12));
lean_inc(v___x_88_);
v___x_90_ = l_Lean_Syntax_isOfKind(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec(v___x_88_);
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v___x_92_ = l_Lean_Syntax_getArg(v___x_88_, v___x_91_);
lean_dec(v___x_88_);
v___x_93_ = ((lean_object*)(l_Lean_Fmt_allowAppArgFill___closed__14));
lean_inc(v___x_92_);
v___x_94_ = l_Lean_Syntax_isOfKind(v___x_92_, v___x_93_);
if (v___x_94_ == 0)
{
lean_dec(v___x_92_);
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = l_Lean_Syntax_getArg(v___x_92_, v___x_87_);
lean_dec(v___x_92_);
v___x_96_ = lean_box(0);
v___x_97_ = l_Lean_Syntax_matchesIdent(v___x_95_, v___x_96_);
lean_dec(v___x_95_);
if (v___x_97_ == 0)
{
lean_dec(v_x_72_);
return v___x_77_;
}
else
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = l_Lean_Syntax_getArg(v_x_72_, v___x_91_);
lean_dec(v_x_72_);
v___x_99_ = l_Lean_Syntax_isOfKind(v___x_98_, v___x_73_);
if (v___x_99_ == 0)
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
}
else
{
uint8_t v___x_100_; 
lean_dec(v_x_72_);
v___x_100_ = 0;
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_allowAppArgFill___boxed(lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Lean_Fmt_allowAppArgFill(v_x_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0(size_t v_sz_104_, size_t v_i_105_, lean_object* v_bs_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = lean_usize_dec_lt(v_i_105_, v_sz_104_);
if (v___x_107_ == 0)
{
return v_bs_106_;
}
else
{
lean_object* v_v_108_; lean_object* v_v_109_; lean_object* v___x_110_; lean_object* v_bs_x27_111_; size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; 
v_v_108_ = lean_array_uget_borrowed(v_bs_106_, v_i_105_);
v_v_109_ = lean_ctor_get(v_v_108_, 0);
lean_inc(v_v_109_);
v___x_110_ = lean_unsigned_to_nat(0u);
v_bs_x27_111_ = lean_array_uset(v_bs_106_, v_i_105_, v___x_110_);
v___x_112_ = ((size_t)1ULL);
v___x_113_ = lean_usize_add(v_i_105_, v___x_112_);
v___x_114_ = lean_array_uset(v_bs_x27_111_, v_i_105_, v_v_109_);
v_i_105_ = v___x_113_;
v_bs_106_ = v___x_114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0___boxed(lean_object* v_sz_116_, lean_object* v_i_117_, lean_object* v_bs_118_){
_start:
{
size_t v_sz_boxed_119_; size_t v_i_boxed_120_; lean_object* v_res_121_; 
v_sz_boxed_119_ = lean_unbox_usize(v_sz_116_);
lean_dec(v_sz_116_);
v_i_boxed_120_ = lean_unbox_usize(v_i_117_);
lean_dec(v_i_117_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0(v_sz_boxed_119_, v_i_boxed_120_, v_bs_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1(size_t v_sz_122_, size_t v_i_123_, lean_object* v_bs_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_usize_dec_lt(v_i_123_, v_sz_122_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_bs_124_);
lean_ctor_set(v___x_128_, 1, v___y_126_);
return v___x_128_;
}
else
{
lean_object* v_v_129_; lean_object* v___x_130_; 
v_v_129_ = lean_array_uget(v_bs_124_, v_i_123_);
lean_inc(v_v_129_);
v___x_130_ = l_Lean_Fmt_fmt(v_v_129_, v___y_125_, v___y_126_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v_a_132_; lean_object* v___x_133_; lean_object* v_bs_x27_134_; uint8_t v___x_135_; lean_object* v___x_136_; size_t v___x_137_; size_t v___x_138_; lean_object* v___x_139_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
v_a_132_ = lean_ctor_get(v___x_130_, 1);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_130_, 2);
v___x_133_ = lean_unsigned_to_nat(0u);
v_bs_x27_134_ = lean_array_uset(v_bs_124_, v_i_123_, v___x_133_);
v___x_135_ = l_Lean_Fmt_allowAppArgFill(v_v_129_);
v___x_136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_136_, 0, v_a_131_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*1, v___x_135_);
v___x_137_ = ((size_t)1ULL);
v___x_138_ = lean_usize_add(v_i_123_, v___x_137_);
v___x_139_ = lean_array_uset(v_bs_x27_134_, v_i_123_, v___x_136_);
v_i_123_ = v___x_138_;
v_bs_124_ = v___x_139_;
v___y_126_ = v_a_132_;
goto _start;
}
else
{
lean_object* v_a_141_; lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_v_129_);
lean_dec_ref(v_bs_124_);
v_a_141_ = lean_ctor_get(v___x_130_, 0);
v_a_142_ = lean_ctor_get(v___x_130_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_130_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_inc(v_a_141_);
lean_dec(v___x_130_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_141_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1___boxed(lean_object* v_sz_150_, lean_object* v_i_151_, lean_object* v_bs_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
size_t v_sz_boxed_155_; size_t v_i_boxed_156_; lean_object* v_res_157_; 
v_sz_boxed_155_ = lean_unbox_usize(v_sz_150_);
lean_dec(v_sz_150_);
v_i_boxed_156_ = lean_unbox_usize(v_i_151_);
lean_dec(v_i_151_);
v_res_157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1(v_sz_boxed_155_, v_i_boxed_156_, v_bs_152_, v___y_153_, v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2(lean_object* v_as_158_, size_t v_i_159_, size_t v_stop_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_eq(v_i_159_, v_stop_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; uint8_t v_allowFill_163_; uint8_t v___x_164_; 
v___x_162_ = lean_array_uget_borrowed(v_as_158_, v_i_159_);
v_allowFill_163_ = lean_ctor_get_uint8(v___x_162_, sizeof(void*)*1);
v___x_164_ = 1;
if (v_allowFill_163_ == 0)
{
return v___x_164_;
}
else
{
if (v___x_161_ == 0)
{
size_t v___x_165_; size_t v___x_166_; 
v___x_165_ = ((size_t)1ULL);
v___x_166_ = lean_usize_add(v_i_159_, v___x_165_);
v_i_159_ = v___x_166_;
goto _start;
}
else
{
return v___x_164_;
}
}
}
else
{
uint8_t v___x_168_; 
v___x_168_ = 0;
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2___boxed(lean_object* v_as_169_, lean_object* v_i_170_, lean_object* v_stop_171_){
_start:
{
size_t v_i_boxed_172_; size_t v_stop_boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_i_boxed_172_ = lean_unbox_usize(v_i_170_);
lean_dec(v_i_170_);
v_stop_boxed_173_ = lean_unbox_usize(v_stop_171_);
lean_dec(v_stop_171_);
v_res_174_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2(v_as_169_, v_i_boxed_172_, v_stop_boxed_173_);
lean_dec_ref(v_as_169_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp_x27(lean_object* v_f_176_, lean_object* v_args_177_, lean_object* v_format_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_args_182_; lean_object* v___y_183_; size_t v_sz_196_; size_t v___x_197_; lean_object* v___x_198_; 
v_sz_196_ = lean_array_size(v_args_177_);
v___x_197_ = ((size_t)0ULL);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__1(v_sz_196_, v___x_197_, v_args_177_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_219_; lean_object* v_array_220_; lean_object* v_start_221_; lean_object* v_stop_222_; lean_object* v___y_224_; uint8_t v___x_229_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc_n(v_a_199_, 2);
v_a_200_ = lean_ctor_get(v___x_198_, 1);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_198_, 2);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_array_get_size(v_a_199_);
v___x_203_ = lean_unsigned_to_nat(1u);
v___x_204_ = lean_nat_sub(v___x_202_, v___x_203_);
lean_inc(v___x_204_);
v___x_219_ = l_Array_toSubarray___redArg(v_a_199_, v___x_201_, v___x_204_);
v_array_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc_ref(v_array_220_);
v_start_221_ = lean_ctor_get(v___x_219_, 1);
lean_inc(v_start_221_);
v_stop_222_ = lean_ctor_get(v___x_219_, 2);
lean_inc(v_stop_222_);
lean_dec_ref(v___x_219_);
v___x_229_ = lean_nat_dec_lt(v_start_221_, v_stop_222_);
if (v___x_229_ == 0)
{
lean_dec(v_stop_222_);
lean_dec(v_start_221_);
lean_dec_ref(v_array_220_);
goto v___jp_205_;
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = lean_array_get_size(v_array_220_);
v___x_231_ = lean_nat_dec_le(v_stop_222_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec(v_stop_222_);
v___y_224_ = v___x_230_;
goto v___jp_223_;
}
else
{
v___y_224_ = v_stop_222_;
goto v___jp_223_;
}
}
v___jp_205_:
{
uint8_t v___x_206_; 
v___x_206_ = lean_nat_dec_lt(v___x_204_, v___x_202_);
if (v___x_206_ == 0)
{
lean_dec(v___x_204_);
v_args_182_ = v_a_199_;
v___y_183_ = v_a_200_;
goto v___jp_181_;
}
else
{
lean_object* v_v_207_; lean_object* v_v_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
v_v_207_ = lean_array_fget(v_a_199_, v___x_204_);
v_v_208_ = lean_ctor_get(v_v_207_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_v_207_);
if (v_isSharedCheck_218_ == 0)
{
v___x_210_ = v_v_207_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_v_208_);
lean_dec(v_v_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v_xs_x27_213_; lean_object* v___x_215_; 
v___x_212_ = lean_box(0);
v_xs_x27_213_ = lean_array_fset(v_a_199_, v___x_204_, v___x_212_);
if (v_isShared_211_ == 0)
{
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_v_208_);
v___x_215_ = v_reuseFailAlloc_217_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; 
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*1, v___x_206_);
v___x_216_ = lean_array_fset(v_xs_x27_213_, v___x_204_, v___x_215_);
lean_dec(v___x_204_);
v_args_182_ = v___x_216_;
v___y_183_ = v_a_200_;
goto v___jp_181_;
}
}
}
}
v___jp_223_:
{
uint8_t v___x_225_; 
v___x_225_ = lean_nat_dec_lt(v_start_221_, v___y_224_);
if (v___x_225_ == 0)
{
lean_dec(v___y_224_);
lean_dec(v_start_221_);
lean_dec_ref(v_array_220_);
goto v___jp_205_;
}
else
{
size_t v___x_226_; size_t v___x_227_; uint8_t v___x_228_; 
v___x_226_ = lean_usize_of_nat(v_start_221_);
lean_dec(v_start_221_);
v___x_227_ = lean_usize_of_nat(v___y_224_);
lean_dec(v___y_224_);
v___x_228_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Fmt_fmtFixedApp_x27_spec__2(v_array_220_, v___x_226_, v___x_227_);
lean_dec_ref(v_array_220_);
if (v___x_228_ == 0)
{
goto v___jp_205_;
}
else
{
lean_dec(v___x_204_);
v_args_182_ = v_a_199_;
v___y_183_ = v_a_200_;
goto v___jp_181_;
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v_f_176_);
v_a_232_ = lean_ctor_get(v___x_198_, 0);
v_a_233_ = lean_ctor_get(v___x_198_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_198_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_inc(v_a_232_);
lean_dec(v___x_198_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_232_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
v___jp_181_:
{
uint8_t v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; size_t v_sz_191_; size_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_184_ = 1;
v___x_185_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_185_, 0, v_f_176_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_mk_empty_array_with_capacity(v___x_186_);
v___x_188_ = lean_array_push(v___x_187_, v___x_185_);
v___x_189_ = l_Array_append___redArg(v___x_188_, v_args_182_);
v___x_190_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_189_, v_format_178_);
lean_dec_ref(v___x_189_);
v_sz_191_ = lean_array_size(v_args_182_);
v___x_192_ = ((size_t)0ULL);
v___x_193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_fmtFixedApp_x27_spec__0(v_sz_191_, v___x_192_, v_args_182_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_190_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___y_183_);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp_x27___boxed(lean_object* v_f_241_, lean_object* v_args_242_, lean_object* v_format_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Fmt_fmtFixedApp_x27(v_f_241_, v_args_242_, v_format_243_, v_a_244_, v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec_ref(v_format_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp(lean_object* v_f_247_, lean_object* v_args_248_, lean_object* v_format_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Fmt_fmtFixedApp_x27(v_f_247_, v_args_248_, v_format_249_, v_a_250_, v_a_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_a_254_ = lean_ctor_get(v___x_252_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v___x_252_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_fst_258_; lean_object* v___x_260_; 
v_fst_258_ = lean_ctor_get(v_a_253_, 0);
lean_inc(v_fst_258_);
lean_dec(v_a_253_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v_fst_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_fst_258_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_a_254_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_263_ = lean_ctor_get(v___x_252_, 0);
v_a_264_ = lean_ctor_get(v___x_252_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_252_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_inc(v_a_263_);
lean_dec(v___x_252_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_263_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFixedApp___boxed(lean_object* v_f_272_, lean_object* v_args_273_, lean_object* v_format_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Fmt_fmtFixedApp(v_f_272_, v_args_273_, v_format_274_, v_a_275_, v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec_ref(v_format_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0___redArg(lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_array_280_; lean_object* v_start_281_; lean_object* v_stop_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_295_; 
v_array_280_ = lean_ctor_get(v_a_278_, 0);
v_start_281_ = lean_ctor_get(v_a_278_, 1);
v_stop_282_ = lean_ctor_get(v_a_278_, 2);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_278_);
if (v_isSharedCheck_295_ == 0)
{
v___x_284_ = v_a_278_;
v_isShared_285_ = v_isSharedCheck_295_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_stop_282_);
lean_inc(v_start_281_);
lean_inc(v_array_280_);
lean_dec(v_a_278_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_295_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_lt(v_start_281_, v_stop_282_);
if (v___x_286_ == 0)
{
lean_del_object(v___x_284_);
lean_dec(v_stop_282_);
lean_dec(v_start_281_);
lean_dec_ref(v_array_280_);
return v_b_279_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_start_281_, v___x_287_);
lean_inc_ref(v_array_280_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_288_);
v___x_290_ = v___x_284_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_array_280_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_stop_282_);
v___x_290_ = v_reuseFailAlloc_294_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_array_fget(v_array_280_, v_start_281_);
lean_dec(v_start_281_);
lean_dec_ref(v_array_280_);
v___x_292_ = lean_array_push(v_b_279_, v___x_291_);
v_a_278_ = v___x_290_;
v_b_279_ = v___x_292_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAppLike(lean_object* v_terms_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = lean_array_get_size(v_terms_304_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_nat_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v_fStx_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_args_316_; lean_object* v_fst_318_; lean_object* v_snd_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_310_ = 1;
v___x_311_ = lean_box(0);
v_fStx_312_ = lean_array_get(v___x_311_, v_terms_304_, v___x_308_);
v___x_313_ = lean_unsigned_to_nat(1u);
v___x_314_ = l_Array_toSubarray___redArg(v_terms_304_, v___x_313_, v___x_307_);
v___x_315_ = ((lean_object*)(l_Lean_Fmt_fmtAppLike___closed__0));
v_args_316_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0___redArg(v___x_314_, v___x_315_);
v___x_362_ = ((lean_object*)(l_Lean_Fmt_fmtAppLike___closed__2));
lean_inc(v_fStx_312_);
v___x_363_ = l_Lean_Syntax_isOfKind(v_fStx_312_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_inc(v_fStx_312_);
v___x_364_ = l_Lean_Fmt_fmt(v_fStx_312_, v_a_305_, v_a_306_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v_a_366_; lean_object* v___x_367_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
v_a_366_ = lean_ctor_get(v___x_364_, 1);
lean_inc(v_a_366_);
lean_dec_ref_known(v___x_364_, 2);
v___x_367_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_367_, 0, v___x_310_);
lean_ctor_set_uint8(v___x_367_, 1, v___x_309_);
lean_ctor_set_uint8(v___x_367_, 2, v___x_310_);
lean_ctor_set_uint8(v___x_367_, 3, v___x_310_);
v_fst_318_ = v_a_365_;
v_snd_319_ = v___x_367_;
v___y_320_ = v_a_305_;
v___y_321_ = v_a_366_;
goto v___jp_317_;
}
else
{
lean_dec_ref(v_args_316_);
lean_dec(v_fStx_312_);
return v___x_364_;
}
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = l_Lean_Syntax_getArg(v_fStx_312_, v___x_308_);
v___x_369_ = l_Lean_Fmt_fmt(v___x_368_, v_a_305_, v_a_306_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v_a_371_; lean_object* v_dotTk_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc_n(v_a_370_, 2);
v_a_371_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_369_, 2);
v_dotTk_372_ = l_Lean_Syntax_getArg(v_fStx_312_, v___x_313_);
v___x_373_ = lean_unsigned_to_nat(2u);
v___x_374_ = l_Lean_Syntax_getArg(v_fStx_312_, v___x_373_);
v___x_375_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_a_370_);
v___x_376_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_376_, 0, v___x_310_);
lean_ctor_set_uint8(v___x_376_, 1, v___x_375_);
lean_ctor_set_uint8(v___x_376_, 2, v___x_310_);
lean_ctor_set_uint8(v___x_376_, 3, v___x_310_);
v___x_377_ = l_Lean_Fmt_fmtProjLike(v_a_370_, v_dotTk_372_, v___x_374_, v_a_305_, v_a_371_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v_a_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
v_a_379_ = lean_ctor_get(v___x_377_, 1);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_377_, 2);
v_fst_318_ = v_a_378_;
v_snd_319_ = v___x_376_;
v___y_320_ = v_a_305_;
v___y_321_ = v_a_379_;
goto v___jp_317_;
}
else
{
lean_dec_ref_known(v___x_376_, 0);
lean_dec_ref(v_args_316_);
lean_dec(v_fStx_312_);
return v___x_377_;
}
}
else
{
lean_dec_ref(v_args_316_);
lean_dec(v_fStx_312_);
return v___x_369_;
}
}
v___jp_317_:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Fmt_fmtFixedApp_x27(v_fst_318_, v_args_316_, v_snd_319_, v___y_320_, v___y_321_);
lean_dec_ref(v_snd_319_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_352_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_a_324_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_352_ == 0)
{
v___x_326_ = v___x_322_;
v_isShared_327_ = v_isSharedCheck_352_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_352_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_fst_328_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_fst_328_);
v_snd_329_ = lean_ctor_get(v_a_323_, 1);
lean_inc(v_snd_329_);
lean_dec(v_a_323_);
v___x_330_ = lean_array_get_size(v_snd_329_);
v___x_331_ = lean_nat_dec_eq(v___x_330_, v___x_313_);
if (v___x_331_ == 0)
{
lean_object* v___x_333_; 
lean_dec(v_snd_329_);
lean_dec(v_fStx_312_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v_fst_328_);
v___x_333_ = v___x_326_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_fst_328_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_a_324_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_336_ = lean_array_get(v___x_335_, v_snd_329_, v___x_308_);
lean_dec(v_snd_329_);
v___x_337_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_336_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v_env_339_; uint8_t v___x_340_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref_known(v___x_337_, 1);
v_env_339_ = lean_ctor_get(v___y_320_, 0);
lean_inc_ref(v_env_339_);
v___x_340_ = l_Lean_Fmt_propagatesRhsStickiness(v_env_339_, v_fStx_312_);
if (v___x_340_ == 0)
{
lean_object* v___x_342_; 
lean_dec(v_val_338_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v_fst_328_);
v___x_342_ = v___x_326_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_fst_328_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_a_324_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
else
{
uint8_t v_kind_344_; lean_object* v___x_345_; lean_object* v___x_347_; 
v_kind_344_ = lean_ctor_get_uint8(v_val_338_, sizeof(void*)*1);
lean_dec(v_val_338_);
lean_inc(v_fst_328_);
v___x_345_ = l_Lean_Fmt_TaggedDoc_sticky(v_fst_328_, v_fst_328_, v_kind_344_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_345_);
v___x_347_ = v___x_326_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_a_324_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v___x_337_);
lean_dec(v_fStx_312_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v_fst_328_);
v___x_350_ = v___x_326_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_fst_328_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_a_324_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_fStx_312_);
v_a_353_ = lean_ctor_get(v___x_322_, 0);
v_a_354_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_322_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_322_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_353_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec_ref(v_terms_304_);
v___x_380_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v_a_306_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAppLike___boxed(lean_object* v_terms_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Fmt_fmtAppLike(v_terms_382_, v_a_383_, v_a_384_);
lean_dec_ref(v_a_383_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0(lean_object* v_inst_386_, lean_object* v_R_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Fmt_fmtAppLike_spec__0___redArg(v_a_388_, v_b_389_);
return v___x_390_;
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
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
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

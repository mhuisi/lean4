// Lean compiler output
// Module: Lean.Fmt.Util.RangeTree
// Imports: public import Lean.Syntax public import Init.While public import Init.Data.Array.QSort.Basic
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* l___private_Init_While_0__repeatM_erased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_Syntax_instInhabitedRange_default;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Fmt.Util.RangeTree"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Fmt.binSearchRightmost"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Fmt.binSearchLeftmost"};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "children"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14;
static const lean_string_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default(lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedRangeTree___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instInhabitedRangeTree___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "roots"};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_compareRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_compareRanges___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__0_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__1_value)}};
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__7_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__2_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__3_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__4_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__5_value)}};
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__8_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__6_value)}};
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__2, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11_value;
static const lean_closure_object l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__3, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9_value),((lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__11_value)} };
static const lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_panic_fn_borrowed(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2));
v___x_8_ = lean_unsigned_to_nat(8u);
v___x_9_ = lean_unsigned_to_nat(35u);
v___x_10_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__1));
v___x_11_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0));
v___x_12_ = l_mkPanicMessageWithDecl(v___x_11_, v___x_10_, v___x_9_, v___x_8_, v___x_7_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(lean_object* v_xs_13_, lean_object* v_key_14_, lean_object* v_lt_15_, lean_object* v_query_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_fst_18_; lean_object* v_snd_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_54_; 
v_fst_18_ = lean_ctor_get(v_a_17_, 0);
v_snd_19_ = lean_ctor_get(v_a_17_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_a_17_);
if (v_isSharedCheck_54_ == 0)
{
v___x_21_ = v_a_17_;
v_isShared_22_ = v_isSharedCheck_54_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snd_19_);
lean_inc(v_fst_18_);
lean_dec(v_a_17_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_54_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
uint8_t v___x_23_; 
v___x_23_ = lean_nat_dec_lt(v_fst_18_, v_snd_19_);
if (v___x_23_ == 0)
{
lean_object* v___x_25_; 
lean_dec(v_query_16_);
lean_dec_ref(v_lt_15_);
lean_dec(v_key_14_);
if (v_isShared_22_ == 0)
{
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_fst_18_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_snd_19_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_28_ = lean_nat_sub(v_snd_19_, v_fst_18_);
v___x_29_ = lean_unsigned_to_nat(1u);
v___x_30_ = lean_nat_shiftr(v___x_28_, v___x_29_);
lean_dec(v___x_28_);
v___x_31_ = lean_nat_add(v_fst_18_, v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_array_get_size(v_xs_13_);
v___x_33_ = lean_nat_dec_lt(v___x_31_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v___x_31_);
v___x_34_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__3);
v___x_35_ = l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(v___x_34_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_36_; 
lean_del_object(v___x_21_);
lean_dec(v_snd_19_);
lean_dec(v_fst_18_);
lean_dec(v_query_16_);
lean_dec_ref(v_lt_15_);
lean_dec(v_key_14_);
v___x_36_ = lean_box(0);
return v___x_36_;
}
else
{
lean_object* v___x_38_; 
lean_dec_ref_known(v___x_35_, 1);
if (v_isShared_22_ == 0)
{
v___x_38_ = v___x_21_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_fst_18_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_snd_19_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
v_a_17_ = v___x_38_;
goto _start;
}
}
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_41_ = lean_array_fget_borrowed(v_xs_13_, v___x_31_);
lean_inc(v_key_14_);
lean_inc(v___x_41_);
v___x_42_ = lean_apply_1(v_key_14_, v___x_41_);
lean_inc_ref(v_lt_15_);
lean_inc(v_query_16_);
v___x_43_ = lean_apply_2(v_lt_15_, v_query_16_, v___x_42_);
v___x_44_ = lean_unbox(v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_47_; 
lean_dec(v_fst_18_);
v___x_45_ = lean_nat_add(v___x_31_, v___x_29_);
lean_dec(v___x_31_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_45_);
v___x_47_ = v___x_21_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_snd_19_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
v_a_17_ = v___x_47_;
goto _start;
}
}
else
{
lean_object* v___x_51_; 
lean_dec(v_snd_19_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 1, v___x_31_);
v___x_51_ = v___x_21_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_fst_18_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_31_);
v___x_51_ = v_reuseFailAlloc_53_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
v_a_17_ = v___x_51_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___boxed(lean_object* v_xs_55_, lean_object* v_key_56_, lean_object* v_lt_57_, lean_object* v_query_58_, lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(v_xs_55_, v_key_56_, v_lt_57_, v_query_58_, v_a_59_);
lean_dec_ref(v_xs_55_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg(lean_object* v_xs_61_, lean_object* v_query_62_, lean_object* v_key_63_, lean_object* v_lt_64_){
_start:
{
lean_object* v_l_65_; lean_object* v_r_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_l_65_ = lean_unsigned_to_nat(0u);
v_r_66_ = lean_array_get_size(v_xs_61_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v_l_65_);
lean_ctor_set(v___x_67_, 1, v_r_66_);
lean_inc(v_query_62_);
lean_inc_ref(v_lt_64_);
lean_inc(v_key_63_);
v___x_68_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(v_xs_61_, v_key_63_, v_lt_64_, v_query_62_, v___x_67_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v___x_69_; 
lean_dec_ref(v_lt_64_);
lean_dec(v_key_63_);
lean_dec(v_query_62_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v_val_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_95_; 
v_val_70_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_95_ == 0)
{
v___x_72_ = v___x_68_;
v_isShared_73_ = v_isSharedCheck_95_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_val_70_);
lean_dec(v___x_68_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_95_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_snd_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_93_; 
v_snd_74_ = lean_ctor_get(v_val_70_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_val_70_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v_val_70_, 0);
lean_dec(v_unused_94_);
v___x_76_ = v_val_70_;
v_isShared_77_ = v_isSharedCheck_93_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_snd_74_);
lean_dec(v_val_70_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_93_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_sub(v_snd_74_, v___x_78_);
lean_dec(v_snd_74_);
v___x_80_ = lean_nat_dec_lt(v___x_79_, v_r_66_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
lean_dec(v___x_79_);
lean_del_object(v___x_76_);
lean_del_object(v___x_72_);
lean_dec_ref(v_lt_64_);
lean_dec(v_key_63_);
lean_dec(v_query_62_);
v___x_81_ = lean_box(0);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_82_ = lean_array_fget_borrowed(v_xs_61_, v___x_79_);
lean_inc(v___x_82_);
v___x_83_ = lean_apply_1(v_key_63_, v___x_82_);
v___x_84_ = lean_apply_2(v_lt_64_, v_query_62_, v___x_83_);
v___x_85_ = lean_unbox(v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_87_; 
lean_inc(v___x_82_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_82_);
lean_ctor_set(v___x_76_, 0, v___x_79_);
v___x_87_ = v___x_76_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_82_);
v___x_87_ = v_reuseFailAlloc_91_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_89_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_87_);
v___x_89_ = v___x_72_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v___x_79_);
lean_del_object(v___x_76_);
lean_del_object(v___x_72_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___redArg___boxed(lean_object* v_xs_96_, lean_object* v_query_97_, lean_object* v_key_98_, lean_object* v_lt_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Fmt_binSearchRightmost___redArg(v_xs_96_, v_query_97_, v_key_98_, v_lt_99_);
lean_dec_ref(v_xs_96_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_xs_103_, lean_object* v_query_104_, lean_object* v_key_105_, lean_object* v_lt_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Fmt_binSearchRightmost___redArg(v_xs_103_, v_query_104_, v_key_105_, v_lt_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchRightmost___boxed(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_xs_110_, lean_object* v_query_111_, lean_object* v_key_112_, lean_object* v_lt_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Fmt_binSearchRightmost(v_00_u03b1_108_, v_00_u03b2_109_, v_xs_110_, v_query_111_, v_key_112_, v_lt_113_);
lean_dec_ref(v_xs_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1(lean_object* v_00_u03b1_115_, lean_object* v_xs_116_, lean_object* v_00_u03b2_117_, lean_object* v_key_118_, lean_object* v_lt_119_, lean_object* v_query_120_, lean_object* v_inst_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg(v_xs_116_, v_key_118_, v_lt_119_, v_query_120_, v_a_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___boxed(lean_object* v_00_u03b1_124_, lean_object* v_xs_125_, lean_object* v_00_u03b2_126_, lean_object* v_key_127_, lean_object* v_lt_128_, lean_object* v_query_129_, lean_object* v_inst_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1(v_00_u03b1_124_, v_xs_125_, v_00_u03b2_126_, v_key_127_, v_lt_128_, v_query_129_, v_inst_130_, v_a_131_);
lean_dec_ref(v_xs_125_);
return v_res_132_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_134_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__2));
v___x_135_ = lean_unsigned_to_nat(8u);
v___x_136_ = lean_unsigned_to_nat(64u);
v___x_137_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__0));
v___x_138_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchRightmost_spec__1___redArg___closed__0));
v___x_139_ = l_mkPanicMessageWithDecl(v___x_138_, v___x_137_, v___x_136_, v___x_135_, v___x_134_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(lean_object* v_xs_140_, lean_object* v_key_141_, lean_object* v_lt_142_, lean_object* v_query_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_fst_145_; lean_object* v_snd_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_181_; 
v_fst_145_ = lean_ctor_get(v_a_144_, 0);
v_snd_146_ = lean_ctor_get(v_a_144_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_a_144_);
if (v_isSharedCheck_181_ == 0)
{
v___x_148_ = v_a_144_;
v_isShared_149_ = v_isSharedCheck_181_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snd_146_);
lean_inc(v_fst_145_);
lean_dec(v_a_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_181_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_lt(v_fst_145_, v_snd_146_);
if (v___x_150_ == 0)
{
lean_object* v___x_152_; 
lean_dec(v_query_143_);
lean_dec_ref(v_lt_142_);
lean_dec(v_key_141_);
if (v_isShared_149_ == 0)
{
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_fst_145_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_snd_146_);
v___x_152_ = v_reuseFailAlloc_154_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_155_ = lean_nat_sub(v_snd_146_, v_fst_145_);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_shiftr(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_nat_add(v_fst_145_, v___x_157_);
lean_dec(v___x_157_);
v___x_159_ = lean_array_get_size(v_xs_140_);
v___x_160_ = lean_nat_dec_lt(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v___x_158_);
v___x_161_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___closed__1);
v___x_162_ = l_panic___at___00Lean_Fmt_binSearchRightmost_spec__0(v___x_161_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v___x_163_; 
lean_del_object(v___x_148_);
lean_dec(v_snd_146_);
lean_dec(v_fst_145_);
lean_dec(v_query_143_);
lean_dec_ref(v_lt_142_);
lean_dec(v_key_141_);
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v___x_165_; 
lean_dec_ref_known(v___x_162_, 1);
if (v_isShared_149_ == 0)
{
v___x_165_ = v___x_148_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_fst_145_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_snd_146_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v_a_144_ = v___x_165_;
goto _start;
}
}
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_168_ = lean_array_fget_borrowed(v_xs_140_, v___x_158_);
lean_inc(v_key_141_);
lean_inc(v___x_168_);
v___x_169_ = lean_apply_1(v_key_141_, v___x_168_);
lean_inc_ref(v_lt_142_);
lean_inc(v_query_143_);
v___x_170_ = lean_apply_2(v_lt_142_, v___x_169_, v_query_143_);
v___x_171_ = lean_unbox(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_173_; 
lean_dec(v_snd_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___x_158_);
v___x_173_ = v___x_148_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_fst_145_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_158_);
v___x_173_ = v_reuseFailAlloc_175_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
v_a_144_ = v___x_173_;
goto _start;
}
}
else
{
lean_object* v___x_176_; lean_object* v___x_178_; 
lean_dec(v_fst_145_);
v___x_176_ = lean_nat_add(v___x_158_, v___x_156_);
lean_dec(v___x_158_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_176_);
v___x_178_ = v___x_148_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v_snd_146_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
v_a_144_ = v___x_178_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg___boxed(lean_object* v_xs_182_, lean_object* v_key_183_, lean_object* v_lt_184_, lean_object* v_query_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(v_xs_182_, v_key_183_, v_lt_184_, v_query_185_, v_a_186_);
lean_dec_ref(v_xs_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg(lean_object* v_xs_188_, lean_object* v_query_189_, lean_object* v_key_190_, lean_object* v_lt_191_){
_start:
{
lean_object* v_l_192_; lean_object* v_r_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v_l_192_ = lean_unsigned_to_nat(0u);
v_r_193_ = lean_array_get_size(v_xs_188_);
v___x_194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_194_, 0, v_l_192_);
lean_ctor_set(v___x_194_, 1, v_r_193_);
lean_inc(v_query_189_);
lean_inc_ref(v_lt_191_);
lean_inc(v_key_190_);
v___x_195_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(v_xs_188_, v_key_190_, v_lt_191_, v_query_189_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v___x_196_; 
lean_dec_ref(v_lt_191_);
lean_dec(v_key_190_);
lean_dec(v_query_189_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v_val_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_220_; 
v_val_197_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_220_ == 0)
{
v___x_199_ = v___x_195_;
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_val_197_);
lean_dec(v___x_195_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_220_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_fst_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_218_; 
v_fst_201_ = lean_ctor_get(v_val_197_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_val_197_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_val_197_, 1);
lean_dec(v_unused_219_);
v___x_203_ = v_val_197_;
v_isShared_204_ = v_isSharedCheck_218_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_fst_201_);
lean_dec(v_val_197_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_218_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_lt(v_fst_201_, v_r_193_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_del_object(v___x_203_);
lean_dec(v_fst_201_);
lean_del_object(v___x_199_);
lean_dec_ref(v_lt_191_);
lean_dec(v_key_190_);
lean_dec(v_query_189_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_207_ = lean_array_fget_borrowed(v_xs_188_, v_fst_201_);
lean_inc(v___x_207_);
v___x_208_ = lean_apply_1(v_key_190_, v___x_207_);
v___x_209_ = lean_apply_2(v_lt_191_, v___x_208_, v_query_189_);
v___x_210_ = lean_unbox(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_212_; 
lean_inc(v___x_207_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_207_);
v___x_212_ = v___x_203_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_fst_201_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_207_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_214_; 
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_212_);
v___x_214_ = v___x_199_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
else
{
lean_object* v___x_217_; 
lean_del_object(v___x_203_);
lean_dec(v_fst_201_);
lean_del_object(v___x_199_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___redArg___boxed(lean_object* v_xs_221_, lean_object* v_query_222_, lean_object* v_key_223_, lean_object* v_lt_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Fmt_binSearchLeftmost___redArg(v_xs_221_, v_query_222_, v_key_223_, v_lt_224_);
lean_dec_ref(v_xs_221_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_xs_228_, lean_object* v_query_229_, lean_object* v_key_230_, lean_object* v_lt_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Fmt_binSearchLeftmost___redArg(v_xs_228_, v_query_229_, v_key_230_, v_lt_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_binSearchLeftmost___boxed(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_xs_235_, lean_object* v_query_236_, lean_object* v_key_237_, lean_object* v_lt_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Fmt_binSearchLeftmost(v_00_u03b1_233_, v_00_u03b2_234_, v_xs_235_, v_query_236_, v_key_237_, v_lt_238_);
lean_dec_ref(v_xs_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0(lean_object* v_00_u03b1_240_, lean_object* v_xs_241_, lean_object* v_00_u03b2_242_, lean_object* v_key_243_, lean_object* v_lt_244_, lean_object* v_query_245_, lean_object* v_inst_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___redArg(v_xs_241_, v_key_243_, v_lt_244_, v_query_245_, v_a_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0___boxed(lean_object* v_00_u03b1_249_, lean_object* v_xs_250_, lean_object* v_00_u03b2_251_, lean_object* v_key_252_, lean_object* v_lt_253_, lean_object* v_query_254_, lean_object* v_inst_255_, lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_binSearchLeftmost_spec__0(v_00_u03b1_249_, v_xs_250_, v_00_u03b2_251_, v_key_252_, v_lt_253_, v_query_254_, v_inst_255_, v_a_256_);
lean_dec_ref(v_xs_250_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(lean_object* v_inst_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = l_Lean_Syntax_instInhabitedRange_default;
v___x_262_ = ((lean_object*)(l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0));
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v_inst_260_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode_default(lean_object* v_00_u03b1_264_, lean_object* v_inst_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(v_inst_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode___redArg(lean_object* v_inst_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(v_inst_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTreeNode(lean_object* v_a_269_, lean_object* v_inst_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg(v_inst_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(9u);
v___x_286_ = lean_nat_to_int(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(12u);
v___x_297_ = lean_nat_to_int(v___x_296_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__0));
v___x_300_ = lean_string_length(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__16);
v___x_302_ = lean_nat_to_int(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___boxed(lean_object* v_inst_307_, lean_object* v_x_308_, lean_object* v_prec_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(v_inst_307_, v_x_308_, v_prec_309_);
lean_dec(v_prec_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(lean_object* v_inst_311_, lean_object* v_x_312_, lean_object* v_prec_313_){
_start:
{
lean_object* v_range_314_; lean_object* v_value_315_; lean_object* v_children_316_; lean_object* v_localinst_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_range_314_ = lean_ctor_get(v_x_312_, 0);
lean_inc_ref(v_range_314_);
v_value_315_ = lean_ctor_get(v_x_312_, 1);
lean_inc(v_value_315_);
v_children_316_ = lean_ctor_get(v_x_312_, 2);
lean_inc_ref(v_children_316_);
lean_dec_ref(v_x_312_);
lean_inc_ref(v_inst_311_);
v_localinst_317_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___boxed), 3, 1);
lean_closure_set(v_localinst_317_, 0, v_inst_311_);
v___x_318_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__5));
v___x_319_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__6));
v___x_320_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = l_Lean_Syntax_instReprRange_repr___redArg(v_range_314_);
v___x_323_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = 0;
v___x_325_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*1, v___x_324_);
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_319_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__9));
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_box(1);
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__11));
v___x_332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_318_);
v___x_334_ = lean_apply_2(v_inst_311_, v_value_315_, v___x_321_);
v___x_335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_320_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*1, v___x_324_);
v___x_337_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_333_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_327_);
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_329_);
v___x_340_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__13));
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_318_);
v___x_343_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__14);
v___x_344_ = l_Array_repr___redArg(v_localinst_317_, v_children_316_);
v___x_345_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*1, v___x_324_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_342_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17);
v___x_349_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18));
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_347_);
v___x_351_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19));
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_348_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_324_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr(lean_object* v_00_u03b1_355_, lean_object* v_inst_356_, lean_object* v_x_357_, lean_object* v_prec_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Fmt_instReprRangeTreeNode_repr___redArg(v_inst_356_, v_x_357_, v_prec_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode_repr___boxed(lean_object* v_00_u03b1_360_, lean_object* v_inst_361_, lean_object* v_x_362_, lean_object* v_prec_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Fmt_instReprRangeTreeNode_repr(v_00_u03b1_360_, v_inst_361_, v_x_362_, v_prec_363_);
lean_dec(v_prec_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode___redArg(lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___boxed), 4, 2);
lean_closure_set(v___x_366_, 0, lean_box(0));
lean_closure_set(v___x_366_, 1, v_inst_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTreeNode(lean_object* v_00_u03b1_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___boxed), 4, 2);
lean_closure_set(v___x_369_, 0, lean_box(0));
lean_closure_set(v___x_369_, 1, v_inst_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree_default(lean_object* v_00_u03b1_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = ((lean_object*)(l_Lean_Fmt_instInhabitedRangeTreeNode_default___redArg___closed__0));
return v___x_371_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedRangeTree___closed__0(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Fmt_instInhabitedRangeTree_default(lean_box(0));
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedRangeTree(lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_obj_once(&l_Lean_Fmt_instInhabitedRangeTree___closed__0, &l_Lean_Fmt_instInhabitedRangeTree___closed__0_once, _init_l_Lean_Fmt_instInhabitedRangeTree___closed__0);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___redArg(lean_object* v_inst_384_, lean_object* v_x_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_386_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTree_repr___redArg___closed__3));
v___x_387_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__7);
v___x_388_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTreeNode_repr___boxed), 4, 2);
lean_closure_set(v___x_388_, 0, lean_box(0));
lean_closure_set(v___x_388_, 1, v_inst_384_);
v___x_389_ = l_Array_repr___redArg(v___x_388_, v_x_385_);
v___x_390_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_387_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = 0;
v___x_392_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*1, v___x_391_);
v___x_393_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_386_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_obj_once(&l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17, &l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17_once, _init_l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__17);
v___x_395_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__18));
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_393_);
v___x_397_ = ((lean_object*)(l_Lean_Fmt_instReprRangeTreeNode_repr___redArg___closed__19));
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_394_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_391_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr(lean_object* v_00_u03b1_401_, lean_object* v_inst_402_, lean_object* v_x_403_, lean_object* v_prec_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Fmt_instReprRangeTree_repr___redArg(v_inst_402_, v_x_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree_repr___boxed(lean_object* v_00_u03b1_406_, lean_object* v_inst_407_, lean_object* v_x_408_, lean_object* v_prec_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Fmt_instReprRangeTree_repr(v_00_u03b1_406_, v_inst_407_, v_x_408_, v_prec_409_);
lean_dec(v_prec_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree___redArg(lean_object* v_inst_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTree_repr___boxed), 4, 2);
lean_closure_set(v___x_412_, 0, lean_box(0));
lean_closure_set(v___x_412_, 1, v_inst_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprRangeTree(lean_object* v_00_u03b1_413_, lean_object* v_inst_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprRangeTree_repr___boxed), 4, 2);
lean_closure_set(v___x_415_, 0, lean_box(0));
lean_closure_set(v___x_415_, 1, v_inst_414_);
return v___x_415_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_compareRanges(lean_object* v_a_416_, lean_object* v_b_417_){
_start:
{
lean_object* v_start_418_; lean_object* v_stop_419_; lean_object* v_start_420_; lean_object* v_stop_421_; uint8_t v___x_422_; 
v_start_418_ = lean_ctor_get(v_a_416_, 0);
v_stop_419_ = lean_ctor_get(v_a_416_, 1);
v_start_420_ = lean_ctor_get(v_b_417_, 0);
v_stop_421_ = lean_ctor_get(v_b_417_, 1);
v___x_422_ = lean_nat_dec_lt(v_start_418_, v_start_420_);
if (v___x_422_ == 0)
{
uint8_t v___x_423_; 
v___x_423_ = lean_nat_dec_eq(v_start_418_, v_start_420_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; 
v___x_424_ = 2;
return v___x_424_;
}
else
{
uint8_t v___x_425_; 
v___x_425_ = lean_nat_dec_lt(v_stop_421_, v_stop_419_);
if (v___x_425_ == 0)
{
uint8_t v___x_426_; 
v___x_426_ = lean_nat_dec_eq(v_stop_421_, v_stop_419_);
if (v___x_426_ == 0)
{
uint8_t v___x_427_; 
v___x_427_ = 2;
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = 1;
return v___x_428_;
}
}
else
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
}
}
else
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_compareRanges___boxed(lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Lean_Fmt_compareRanges(v_a_431_, v_b_432_);
lean_dec_ref(v_b_432_);
lean_dec_ref(v_a_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(lean_object* v_entries_437_, lean_object* v_fst_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_fst_440_; lean_object* v_snd_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_486_; 
v_fst_440_ = lean_ctor_get(v_a_439_, 0);
v_snd_441_ = lean_ctor_get(v_a_439_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_486_ == 0)
{
v___x_443_ = v_a_439_;
v_isShared_444_ = v_isSharedCheck_486_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_snd_441_);
lean_inc(v_fst_440_);
lean_dec(v_a_439_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_486_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = lean_array_get_size(v_entries_437_);
v___x_446_ = lean_nat_dec_lt(v_snd_441_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_448_; 
if (v_isShared_444_ == 0)
{
v___x_448_ = v___x_443_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_fst_440_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_snd_441_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
lean_object* v___x_450_; lean_object* v_fst_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_484_; 
lean_del_object(v___x_443_);
v___x_450_ = lean_array_fget(v_entries_437_, v_snd_441_);
v_fst_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; 
v_unused_485_ = lean_ctor_get(v___x_450_, 1);
lean_dec(v_unused_485_);
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_484_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_fst_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_484_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_455_ = 0;
v___x_456_ = l_Lean_Syntax_Range_includes(v_fst_438_, v_fst_451_, v___x_455_, v___x_455_);
lean_dec(v_fst_451_);
if (v___x_456_ == 0)
{
lean_object* v___x_458_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v_snd_441_);
lean_ctor_set(v___x_453_, 0, v_fst_440_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_fst_440_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_snd_441_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v___x_460_; lean_object* v_snd_461_; 
lean_del_object(v___x_453_);
v___x_460_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v_entries_437_, v_snd_441_);
v_snd_461_ = lean_ctor_get(v___x_460_, 1);
lean_inc(v_snd_461_);
if (lean_obj_tag(v_snd_461_) == 1)
{
lean_object* v_fst_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_472_; 
v_fst_462_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v___x_460_, 1);
lean_dec(v_unused_473_);
v___x_464_ = v___x_460_;
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_fst_462_);
lean_dec(v___x_460_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_472_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_val_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v_val_466_ = lean_ctor_get(v_snd_461_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v_snd_461_, 1);
v___x_467_ = lean_array_push(v_fst_440_, v_val_466_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v_fst_462_);
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_fst_462_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_a_439_ = v___x_469_;
goto _start;
}
}
}
else
{
lean_object* v_fst_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
lean_dec(v_snd_461_);
v_fst_474_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___x_460_, 1);
lean_dec(v_unused_483_);
v___x_476_ = v___x_460_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_fst_474_);
lean_dec(v___x_460_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_fst_474_);
lean_ctor_set(v___x_476_, 0, v_fst_440_);
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_fst_440_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_fst_474_);
v___x_479_ = v_reuseFailAlloc_481_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
v_a_439_ = v___x_479_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(lean_object* v_entries_487_, lean_object* v_i_488_){
_start:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_array_get_size(v_entries_487_);
v___x_490_ = lean_nat_dec_lt(v_i_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_i_488_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v_fst_494_; lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_517_; 
v___x_493_ = lean_array_fget(v_entries_487_, v_i_488_);
v_fst_494_ = lean_ctor_get(v___x_493_, 0);
v_snd_495_ = lean_ctor_get(v___x_493_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_517_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_517_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_inc(v_fst_494_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_517_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_children_499_; lean_object* v___x_500_; lean_object* v_i_501_; lean_object* v___x_503_; 
v_children_499_ = ((lean_object*)(l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___closed__0));
v___x_500_ = lean_unsigned_to_nat(1u);
v_i_501_ = lean_nat_add(v_i_488_, v___x_500_);
lean_dec(v_i_488_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v_i_501_);
lean_ctor_set(v___x_497_, 0, v_children_499_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_children_499_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_i_501_);
v___x_503_ = v_reuseFailAlloc_516_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v_fst_505_; lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
v___x_504_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(v_entries_487_, v_fst_494_, v___x_503_);
v_fst_505_ = lean_ctor_get(v___x_504_, 0);
v_snd_506_ = lean_ctor_get(v___x_504_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_515_ == 0)
{
v___x_508_ = v___x_504_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_inc(v_fst_505_);
lean_dec(v___x_504_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_510_, 0, v_fst_494_);
lean_ctor_set(v___x_510_, 1, v_snd_495_);
lean_ctor_set(v___x_510_, 2, v_fst_505_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v___x_511_);
lean_ctor_set(v___x_508_, 0, v_snd_506_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_snd_506_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg___boxed(lean_object* v_entries_518_, lean_object* v_i_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v_entries_518_, v_i_519_);
lean_dec_ref(v_entries_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg___boxed(lean_object* v_entries_521_, lean_object* v_fst_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(v_entries_521_, v_fst_522_, v_a_523_);
lean_dec_ref(v_fst_522_);
lean_dec_ref(v_entries_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go(lean_object* v_00_u03b1_525_, lean_object* v_entries_526_, lean_object* v_i_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v_entries_526_, v_i_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___boxed(lean_object* v_00_u03b1_529_, lean_object* v_entries_530_, lean_object* v_i_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go(v_00_u03b1_529_, v_entries_530_, v_i_531_);
lean_dec_ref(v_entries_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0(lean_object* v_00_u03b1_533_, lean_object* v_entries_534_, lean_object* v_fst_535_, lean_object* v_inst_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___redArg(v_entries_534_, v_fst_535_, v_a_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0___boxed(lean_object* v_00_u03b1_539_, lean_object* v_entries_540_, lean_object* v_fst_541_, lean_object* v_inst_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go_spec__0(v_00_u03b1_539_, v_entries_540_, v_fst_541_, v_inst_542_, v_a_543_);
lean_dec_ref(v_fst_541_);
lean_dec_ref(v_entries_540_);
return v_res_544_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_fst_547_; lean_object* v_fst_548_; uint8_t v___x_549_; uint8_t v___x_550_; uint8_t v___x_551_; 
v_fst_547_ = lean_ctor_get(v_x_545_, 0);
v_fst_548_ = lean_ctor_get(v_x_546_, 0);
v___x_549_ = l_Lean_Fmt_compareRanges(v_fst_547_, v_fst_548_);
v___x_550_ = 0;
v___x_551_ = l_instDecidableEqOrdering(v___x_549_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0___boxed(lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__0(v_x_552_, v_x_553_);
lean_dec_ref(v_x_553_);
lean_dec_ref(v_x_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1(lean_object* v___y_556_, lean_object* v_b_557_){
_start:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_560_; lean_object* v_snd_561_; 
v_fst_558_ = lean_ctor_get(v_b_557_, 0);
lean_inc(v_fst_558_);
v_snd_559_ = lean_ctor_get(v_b_557_, 1);
lean_inc_n(v_snd_559_, 2);
lean_dec_ref(v_b_557_);
v___x_560_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_ofHashMap_go___redArg(v___y_556_, v_snd_559_);
v_snd_561_ = lean_ctor_get(v___x_560_, 1);
lean_inc(v_snd_561_);
if (lean_obj_tag(v_snd_561_) == 1)
{
lean_object* v_fst_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_578_; 
lean_dec(v_snd_559_);
v_fst_562_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v___x_560_, 1);
lean_dec(v_unused_579_);
v___x_564_ = v___x_560_;
v_isShared_565_ = v_isSharedCheck_578_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_fst_562_);
lean_dec(v___x_560_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_578_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_val_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_577_; 
v_val_566_ = lean_ctor_get(v_snd_561_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_snd_561_);
if (v_isSharedCheck_577_ == 0)
{
v___x_568_ = v_snd_561_;
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_val_566_);
lean_dec(v_snd_561_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_577_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_570_ = lean_array_push(v_fst_558_, v_val_566_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_fst_562_);
lean_ctor_set(v___x_564_, 0, v___x_570_);
v___x_572_ = v___x_564_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_fst_562_);
v___x_572_ = v_reuseFailAlloc_576_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set_tag(v___x_568_, 0);
lean_ctor_set(v___x_568_, 0, v___x_572_);
v___x_574_ = v___x_568_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_snd_561_);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; lean_object* v_unused_589_; 
v_unused_588_ = lean_ctor_get(v___x_560_, 1);
lean_dec(v_unused_588_);
v_unused_589_ = lean_ctor_get(v___x_560_, 0);
lean_dec(v_unused_589_);
v___x_581_ = v___x_560_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_dec(v___x_560_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_snd_559_);
lean_ctor_set(v___x_581_, 0, v_fst_558_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_fst_558_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_snd_559_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1___boxed(lean_object* v___y_590_, lean_object* v_b_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1(v___y_590_, v_b_591_);
lean_dec_ref(v___y_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__2(lean_object* v_x1_593_, lean_object* v_x2_594_, lean_object* v_x3_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_x2_594_);
lean_ctor_set(v___x_596_, 1, v_x3_595_);
v___x_597_ = lean_array_push(v_x1_593_, v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__3(lean_object* v___x_598_, lean_object* v___f_599_, lean_object* v_acc_600_, lean_object* v_l_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_598_, v___f_599_, v_acc_600_, v_l_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___redArg(lean_object* v_entries_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v_size_637_; lean_object* v_buckets_638_; lean_object* v___f_639_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_655_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_628_ = ((lean_object*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__9));
v_size_637_ = lean_ctor_get(v_entries_627_, 0);
lean_inc(v_size_637_);
v_buckets_638_ = lean_ctor_get(v_entries_627_, 1);
lean_inc_ref(v_buckets_638_);
lean_dec_ref(v_entries_627_);
v___f_639_ = ((lean_object*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__10));
v___x_662_ = lean_mk_empty_array_with_capacity(v_size_637_);
lean_dec(v_size_637_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_array_get_size(v_buckets_638_);
v___x_665_ = lean_nat_dec_lt(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec_ref(v_buckets_638_);
v___y_655_ = v___x_662_;
goto v___jp_654_;
}
else
{
lean_object* v___f_666_; uint8_t v___x_667_; 
v___f_666_ = ((lean_object*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___closed__12));
v___x_667_ = lean_nat_dec_le(v___x_664_, v___x_664_);
if (v___x_667_ == 0)
{
if (v___x_665_ == 0)
{
lean_dec_ref(v_buckets_638_);
v___y_655_ = v___x_662_;
goto v___jp_654_;
}
else
{
size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_664_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_628_, v___f_666_, v_buckets_638_, v___x_668_, v___x_669_, v___x_662_);
v___y_655_ = v___x_670_;
goto v___jp_654_;
}
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_664_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_628_, v___f_666_, v_buckets_638_, v___x_671_, v___x_672_, v___x_662_);
v___y_655_ = v___x_673_;
goto v___jp_654_;
}
}
v___jp_629_:
{
lean_object* v___f_632_; lean_object* v_roots_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_fst_636_; 
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Fmt_RangeTree_ofHashMap___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_632_, 0, v___y_631_);
v_roots_633_ = lean_mk_empty_array_with_capacity(v___y_630_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_roots_633_);
lean_ctor_set(v___x_634_, 1, v___y_630_);
v___x_635_ = l___private_Init_While_0__repeatM_erased___redArg(v___x_628_, v___f_632_, v___x_634_);
v_fst_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_fst_636_);
lean_dec(v___x_635_);
return v_fst_636_;
}
v___jp_640_:
{
lean_object* v___x_646_; 
v___x_646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(lean_box(0), v___f_639_, v___y_643_, v___y_641_, v___y_642_, v___y_645_, lean_box(0), lean_box(0), lean_box(0));
lean_dec(v___y_645_);
lean_dec(v___y_643_);
v___y_630_ = v___y_644_;
v___y_631_ = v___x_646_;
goto v___jp_629_;
}
v___jp_647_:
{
uint8_t v___x_653_; 
v___x_653_ = lean_nat_dec_le(v___y_652_, v___y_651_);
if (v___x_653_ == 0)
{
lean_dec(v___y_651_);
lean_inc(v___y_652_);
v___y_641_ = v___y_648_;
v___y_642_ = v___y_652_;
v___y_643_ = v___y_649_;
v___y_644_ = v___y_650_;
v___y_645_ = v___y_652_;
goto v___jp_640_;
}
else
{
v___y_641_ = v___y_648_;
v___y_642_ = v___y_652_;
v___y_643_ = v___y_649_;
v___y_644_ = v___y_650_;
v___y_645_ = v___y_651_;
goto v___jp_640_;
}
}
v___jp_654_:
{
lean_object* v_i_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_i_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v___y_655_);
v___x_658_ = lean_nat_dec_eq(v___x_657_, v_i_656_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_nat_sub(v___x_657_, v___x_659_);
v___x_661_ = lean_nat_dec_le(v_i_656_, v___x_660_);
if (v___x_661_ == 0)
{
lean_inc(v___x_660_);
v___y_648_ = v___y_655_;
v___y_649_ = v___x_657_;
v___y_650_ = v_i_656_;
v___y_651_ = v___x_660_;
v___y_652_ = v___x_660_;
goto v___jp_647_;
}
else
{
v___y_648_ = v___y_655_;
v___y_649_ = v___x_657_;
v___y_650_ = v_i_656_;
v___y_651_ = v___x_660_;
v___y_652_ = v_i_656_;
goto v___jp_647_;
}
}
else
{
v___y_630_ = v_i_656_;
v___y_631_ = v___y_655_;
goto v___jp_629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap(lean_object* v_00_u03b1_674_, lean_object* v_inst_675_, lean_object* v_entries_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Fmt_RangeTree_ofHashMap___redArg(v_entries_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_ofHashMap___boxed(lean_object* v_00_u03b1_678_, lean_object* v_inst_679_, lean_object* v_entries_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Fmt_RangeTree_ofHashMap(v_00_u03b1_678_, v_inst_679_, v_entries_680_);
lean_dec(v_inst_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0(lean_object* v_x_682_){
_start:
{
lean_object* v_range_683_; 
v_range_683_ = lean_ctor_get(v_x_682_, 0);
lean_inc_ref(v_range_683_);
return v_range_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0___boxed(lean_object* v_x_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__0(v_x_684_);
lean_dec_ref(v_x_684_);
return v_res_685_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1(lean_object* v_x1_686_, lean_object* v_x2_687_){
_start:
{
lean_object* v_start_688_; lean_object* v_start_689_; uint8_t v___x_690_; 
v_start_688_ = lean_ctor_get(v_x1_686_, 0);
v_start_689_ = lean_ctor_get(v_x2_687_, 0);
v___x_690_ = lean_nat_dec_lt(v_start_688_, v_start_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1___boxed(lean_object* v_x1_691_, lean_object* v_x2_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___lam__1(v_x1_691_, v_x2_692_);
lean_dec_ref(v_x2_692_);
lean_dec_ref(v_x1_691_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(lean_object* v_children_697_, lean_object* v_range_698_){
_start:
{
lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___x_701_; 
v___f_699_ = ((lean_object*)(l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__0));
v___f_700_ = ((lean_object*)(l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___closed__1));
v___x_701_ = l_Lean_Fmt_binSearchRightmost___redArg(v_children_697_, v_range_698_, v___f_699_, v___f_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_702_; 
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_val_703_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_711_ == 0)
{
v___x_705_ = v___x_701_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_val_703_);
lean_dec(v___x_701_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_snd_707_; lean_object* v___x_709_; 
v_snd_707_ = lean_ctor_get(v_val_703_, 1);
lean_inc(v_snd_707_);
lean_dec(v_val_703_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v_snd_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_snd_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg___boxed(lean_object* v_children_712_, lean_object* v_range_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_children_712_, v_range_713_);
lean_dec_ref(v_children_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining(lean_object* v_00_u03b1_715_, lean_object* v_children_716_, lean_object* v_range_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_children_716_, v_range_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___boxed(lean_object* v_00_u03b1_719_, lean_object* v_children_720_, lean_object* v_range_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining(v_00_u03b1_719_, v_children_720_, v_range_721_);
lean_dec_ref(v_children_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(lean_object* v_range_723_, lean_object* v_t_724_){
_start:
{
lean_object* v_range_725_; lean_object* v_value_726_; lean_object* v_children_727_; uint8_t v___x_728_; uint8_t v___x_729_; 
v_range_725_ = lean_ctor_get(v_t_724_, 0);
v_value_726_ = lean_ctor_get(v_t_724_, 1);
v_children_727_ = lean_ctor_get(v_t_724_, 2);
v___x_728_ = 0;
v___x_729_ = l_Lean_Syntax_Range_includes(v_range_725_, v_range_723_, v___x_728_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec_ref(v_range_723_);
v___x_730_ = lean_box(0);
return v___x_730_;
}
else
{
lean_object* v___x_731_; 
lean_inc_ref(v_range_723_);
v___x_731_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_children_727_, v_range_723_);
if (lean_obj_tag(v___x_731_) == 1)
{
lean_object* v_val_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_741_; 
v_val_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_741_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_val_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_736_; 
v___x_736_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_723_, v_val_732_);
lean_dec(v_val_732_);
if (lean_obj_tag(v___x_736_) == 1)
{
lean_del_object(v___x_734_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec(v___x_736_);
lean_inc(v_value_726_);
lean_inc_ref(v_range_725_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_range_725_);
lean_ctor_set(v___x_737_, 1, v_value_726_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_737_);
v___x_739_ = v___x_734_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v___x_731_);
lean_dec_ref(v_range_723_);
lean_inc(v_value_726_);
lean_inc_ref(v_range_725_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_range_725_);
lean_ctor_set(v___x_742_, 1, v_value_726_);
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg___boxed(lean_object* v_range_744_, lean_object* v_t_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_744_, v_t_745_);
lean_dec_ref(v_t_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go(lean_object* v_00_u03b1_747_, lean_object* v_range_748_, lean_object* v_t_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_748_, v_t_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___boxed(lean_object* v_00_u03b1_751_, lean_object* v_range_752_, lean_object* v_t_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go(v_00_u03b1_751_, v_range_752_, v_t_753_);
lean_dec_ref(v_t_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(lean_object* v_t_755_, lean_object* v_range_756_){
_start:
{
lean_object* v___x_757_; 
lean_inc_ref(v_range_756_);
v___x_757_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_findChildContaining___redArg(v_t_755_, v_range_756_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v___x_758_; 
lean_dec_ref(v_range_756_);
v___x_758_ = lean_box(0);
return v___x_758_;
}
else
{
lean_object* v_val_759_; lean_object* v___x_760_; 
v_val_759_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v___x_757_, 1);
v___x_760_ = l___private_Lean_Fmt_Util_RangeTree_0__Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f_go___redArg(v_range_756_, v_val_759_);
lean_dec(v_val_759_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg___boxed(lean_object* v_t_761_, lean_object* v_range_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(v_t_761_, v_range_762_);
lean_dec_ref(v_t_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f(lean_object* v_00_u03b1_764_, lean_object* v_inst_765_, lean_object* v_t_766_, lean_object* v_range_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___redArg(v_t_766_, v_range_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f___boxed(lean_object* v_00_u03b1_769_, lean_object* v_inst_770_, lean_object* v_t_771_, lean_object* v_range_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Fmt_RangeTree_findSmallestRangeContaining_x3f(v_00_u03b1_769_, v_inst_770_, v_t_771_, v_range_772_);
lean_dec_ref(v_t_771_);
lean_dec(v_inst_770_);
return v_res_773_;
}
}
lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_QSort_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Syntax(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Array_QSort_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Util_RangeTree(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_QSort_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Util_RangeTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Util_RangeTree(builtin);
}
#ifdef __cplusplus
}
#endif

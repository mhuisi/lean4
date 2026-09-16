// Lean compiler output
// Module: Lean.Fmt.FmtM.Primitives
// Imports: public import Lean.Fmt.FmtM.Attribute import Init.Data.Range.Polymorphic.Iterators
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
lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNl___redArg();
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_DefaultCost_ofOverflowFallbackPenalty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object*);
lean_object* l_Lean_Fmt_DefaultCost_ofFailureFallbackPenalty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object*);
lean_object* l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_break___redArg();
lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_empty___redArg();
uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillSomeUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_nl___redArg();
lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_nested(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_hardNested(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isTagged(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isTagged___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateMetaData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_failure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_failure___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_failure;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_newline(lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_nl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_nl___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_nl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_nl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nl;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_break___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_break___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_break___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_break___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_break;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_hardNl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_hardNl___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_hardNl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_hardNl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_empty___closed__0;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_empty;
static const lean_string_object l_Lean_Fmt_TaggedDoc_space___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Fmt_TaggedDoc_space___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_space___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_space___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_space___closed__1;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_space___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_space___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_space;
static const lean_closure_object l_Lean_Fmt_TaggedDoc_nested___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_nested, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_nested___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_nested___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_hardNested___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_hardNested, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_hardNested___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_hardNested___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_doublyNested(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_unflattenable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_unflattenable___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_unflattenable___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_unflattenable___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_flattened___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_flattened___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_flattened___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_flattened___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_maybeFlattened, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_final___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_final___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_final___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_final___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_final(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_initial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_initial___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_initial___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_initial___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_initial(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_free___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_free___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_free___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_free___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_either(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_oneOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_oneOf___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_oneOf___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_oneOf___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnFailure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_softSpace___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_softSpace___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_softSpace;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_join___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_join___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_join___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_join___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_fill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fill___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_fill___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_fill___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_fillUsingSpace___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0;
static const lean_array_object l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isCompoundAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isCompoundAtomic___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instAppend___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instAppend___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instAppend___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instAppend = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instAppend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instBEqStickynessKind___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "TaggedDoc"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Sticky"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__3_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(205, 5, 96, 39, 91, 152, 112, 68)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNameSticky = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__4_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_sticky___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_sticky___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_sticky___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_sticky___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeSep___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_pushElem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SelfDelimited"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(34, 26, 55, 159, 203, 232, 93, 63)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNameSelfDelimited = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14__value;
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isSelfDelimited___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isBracketed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "RawFallback"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(140, 220, 156, 110, 255, 164, 127, 186)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNameRawFallback = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isRawFallback___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PseudoAligned"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value),LEAN_SCALAR_PTR_LITERAL(150, 251, 114, 148, 186, 139, 99, 103)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNamePseudoAligned = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13__value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_pseudoAligned___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_pseudoAligned___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isPseudoAligned(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isPseudoAligned___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_needsAppBrackets___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented;
static const lean_string_object l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "PseudoDedented"};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_0),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_1),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__2_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(230, 34, 149, 200, 47, 241, 128, 242)}};
static const lean_ctor_object l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value_aux_2),((lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__0_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(219, 198, 72, 169, 175, 159, 157, 176)}};
static const lean_object* l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_ = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_TaggedDoc_instTypeNamePseudoDedented = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instImpl___closed__1_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14__value;
static const lean_closure_object l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_propagateMetaData, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object* v_doc_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_doc_1_);
lean_ctor_set(v___x_3_, 1, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(lean_object* v_freshTagId_4_, uint8_t v_kind_5_, lean_object* v_x_6_){
_start:
{
if (lean_obj_tag(v_x_6_) == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_mk_empty_array_with_capacity(v___x_7_);
v___x_9_ = lean_array_push(v___x_8_, v_freshTagId_4_);
v___x_10_ = lean_box(v_kind_5_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v_val_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_30_; 
v_val_13_ = lean_ctor_get(v_x_6_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_6_);
if (v_isSharedCheck_30_ == 0)
{
v___x_15_ = v_x_6_;
v_isShared_16_ = v_isSharedCheck_30_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_val_13_);
lean_dec(v_x_6_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_30_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v_fst_17_; lean_object* v_snd_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_29_; 
v_fst_17_ = lean_ctor_get(v_val_13_, 0);
v_snd_18_ = lean_ctor_get(v_val_13_, 1);
v_isSharedCheck_29_ = !lean_is_exclusive(v_val_13_);
if (v_isSharedCheck_29_ == 0)
{
v___x_20_ = v_val_13_;
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_snd_18_);
lean_inc(v_fst_17_);
lean_dec(v_val_13_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_29_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; lean_object* v___x_24_; 
v___x_22_ = lean_array_push(v_fst_17_, v_freshTagId_4_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_22_);
v___x_24_ = v___x_20_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_22_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_snd_18_);
v___x_24_ = v_reuseFailAlloc_28_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_26_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_24_);
v___x_26_ = v___x_15_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0___boxed(lean_object* v_freshTagId_31_, lean_object* v_kind_32_, lean_object* v_x_33_){
_start:
{
uint8_t v_kind_boxed_34_; lean_object* v_res_35_; 
v_kind_boxed_34_ = lean_unbox(v_kind_32_);
v_res_35_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_31_, v_kind_boxed_34_, v_x_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(lean_object* v_freshTagId_36_, uint8_t v_kind_37_, lean_object* v_a_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_val_42_; lean_object* v___x_43_; 
v___x_40_ = lean_box(0);
v___x_41_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_36_, v_kind_37_, v___x_40_);
v_val_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_val_42_);
lean_dec(v___x_41_);
v___x_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_43_, 0, v_a_38_);
lean_ctor_set(v___x_43_, 1, v_val_42_);
lean_ctor_set(v___x_43_, 2, v_x_39_);
return v___x_43_;
}
else
{
lean_object* v_key_44_; lean_object* v_value_45_; lean_object* v_tail_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_61_; 
v_key_44_ = lean_ctor_get(v_x_39_, 0);
v_value_45_ = lean_ctor_get(v_x_39_, 1);
v_tail_46_ = lean_ctor_get(v_x_39_, 2);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_61_ == 0)
{
v___x_48_ = v_x_39_;
v_isShared_49_ = v_isSharedCheck_61_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_tail_46_);
lean_inc(v_value_45_);
lean_inc(v_key_44_);
lean_dec(v_x_39_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_61_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
uint8_t v___x_50_; 
v___x_50_ = l_Lean_Syntax_instBEqRange_beq(v_key_44_, v_a_38_);
if (v___x_50_ == 0)
{
lean_object* v_tail_51_; lean_object* v___x_53_; 
v_tail_51_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_36_, v_kind_37_, v_a_38_, v_tail_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 2, v_tail_51_);
v___x_53_ = v___x_48_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_key_44_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_value_45_);
lean_ctor_set(v_reuseFailAlloc_54_, 2, v_tail_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_val_57_; lean_object* v___x_59_; 
lean_dec(v_key_44_);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_value_45_);
v___x_56_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___lam__0(v_freshTagId_36_, v_kind_37_, v___x_55_);
v_val_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_val_57_);
lean_dec(v___x_56_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 1, v_val_57_);
lean_ctor_set(v___x_48_, 0, v_a_38_);
v___x_59_ = v___x_48_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_38_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_val_57_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v_tail_46_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2___boxed(lean_object* v_freshTagId_62_, lean_object* v_kind_63_, lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_kind_boxed_66_; lean_object* v_res_67_; 
v_kind_boxed_66_ = lean_unbox(v_kind_63_);
v_res_67_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_62_, v_kind_boxed_66_, v_a_64_, v_x_65_);
return v_res_67_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 0;
return v___x_70_;
}
else
{
lean_object* v_key_71_; lean_object* v_tail_72_; uint8_t v___x_73_; 
v_key_71_ = lean_ctor_get(v_x_69_, 0);
v_tail_72_ = lean_ctor_get(v_x_69_, 2);
v___x_73_ = l_Lean_Syntax_instBEqRange_beq(v_key_71_, v_a_68_);
if (v___x_73_ == 0)
{
v_x_69_ = v_tail_72_;
goto _start;
}
else
{
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg___boxed(lean_object* v_a_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_75_, v_x_76_);
lean_dec(v_x_76_);
lean_dec_ref(v_a_75_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_79_, lean_object* v_x_80_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
return v_x_79_;
}
else
{
lean_object* v_key_81_; lean_object* v_value_82_; lean_object* v_tail_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_106_; 
v_key_81_ = lean_ctor_get(v_x_80_, 0);
v_value_82_ = lean_ctor_get(v_x_80_, 1);
v_tail_83_ = lean_ctor_get(v_x_80_, 2);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_106_ == 0)
{
v___x_85_ = v_x_80_;
v_isShared_86_ = v_isSharedCheck_106_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_tail_83_);
lean_inc(v_value_82_);
lean_inc(v_key_81_);
lean_dec(v_x_80_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_106_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; uint64_t v___x_90_; uint64_t v_fold_91_; uint64_t v___x_92_; uint64_t v___x_93_; uint64_t v___x_94_; size_t v___x_95_; size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_87_ = lean_array_get_size(v_x_79_);
v___x_88_ = l_Lean_Syntax_instHashableRange_hash(v_key_81_);
v___x_89_ = 32ULL;
v___x_90_ = lean_uint64_shift_right(v___x_88_, v___x_89_);
v_fold_91_ = lean_uint64_xor(v___x_88_, v___x_90_);
v___x_92_ = 16ULL;
v___x_93_ = lean_uint64_shift_right(v_fold_91_, v___x_92_);
v___x_94_ = lean_uint64_xor(v_fold_91_, v___x_93_);
v___x_95_ = lean_uint64_to_usize(v___x_94_);
v___x_96_ = lean_usize_of_nat(v___x_87_);
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_sub(v___x_96_, v___x_97_);
v___x_99_ = lean_usize_land(v___x_95_, v___x_98_);
v___x_100_ = lean_array_uget_borrowed(v_x_79_, v___x_99_);
lean_inc(v___x_100_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 2, v___x_100_);
v___x_102_ = v___x_85_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_key_81_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_value_82_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v___x_100_);
v___x_102_ = v_reuseFailAlloc_105_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; 
v___x_103_ = lean_array_uset(v_x_79_, v___x_99_, v___x_102_);
v_x_79_ = v___x_103_;
v_x_80_ = v_tail_83_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(lean_object* v_i_107_, lean_object* v_source_108_, lean_object* v_target_109_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_array_get_size(v_source_108_);
v___x_111_ = lean_nat_dec_lt(v_i_107_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec_ref(v_source_108_);
lean_dec(v_i_107_);
return v_target_109_;
}
else
{
lean_object* v_es_112_; lean_object* v___x_113_; lean_object* v_source_114_; lean_object* v_target_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_es_112_ = lean_array_fget(v_source_108_, v_i_107_);
v___x_113_ = lean_box(0);
v_source_114_ = lean_array_fset(v_source_108_, v_i_107_, v___x_113_);
v_target_115_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(v_target_109_, v_es_112_);
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_add(v_i_107_, v___x_116_);
lean_dec(v_i_107_);
v_i_107_ = v___x_117_;
v_source_108_ = v_source_114_;
v_target_109_ = v_target_115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(lean_object* v_data_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_nbuckets_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_120_ = lean_array_get_size(v_data_119_);
v___x_121_ = lean_unsigned_to_nat(2u);
v_nbuckets_122_ = lean_nat_mul(v___x_120_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_box(0);
v___x_125_ = lean_mk_array(v_nbuckets_122_, v___x_124_);
v___x_126_ = lean_array_propagate_mark(v_data_119_, v___x_125_);
v___x_127_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v___x_123_, v_data_119_, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(lean_object* v_freshTagId_128_, uint8_t v_kind_129_, lean_object* v_m_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_size_132_; lean_object* v_buckets_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_185_; 
v_size_132_ = lean_ctor_get(v_m_130_, 0);
v_buckets_133_ = lean_ctor_get(v_m_130_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_m_130_);
if (v_isSharedCheck_185_ == 0)
{
v___x_135_ = v_m_130_;
v_isShared_136_ = v_isSharedCheck_185_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_buckets_133_);
lean_inc(v_size_132_);
lean_dec(v_m_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_185_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_bkt_150_; uint8_t v___x_151_; 
v___x_137_ = lean_array_get_size(v_buckets_133_);
v___x_138_ = l_Lean_Syntax_instHashableRange_hash(v_a_131_);
v___x_139_ = 32ULL;
v___x_140_ = lean_uint64_shift_right(v___x_138_, v___x_139_);
v_fold_141_ = lean_uint64_xor(v___x_138_, v___x_140_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_137_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v_bkt_150_ = lean_array_uget_borrowed(v_buckets_133_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_131_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v_size_x27_157_; lean_object* v___x_158_; lean_object* v_buckets_x27_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_array_push(v___x_153_, v_freshTagId_128_);
v___x_155_ = lean_box(v_kind_129_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set(v___x_156_, 1, v___x_155_);
v_size_x27_157_ = lean_nat_add(v_size_132_, v___x_152_);
lean_dec(v_size_132_);
lean_inc(v_bkt_150_);
v___x_158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_158_, 0, v_a_131_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
lean_ctor_set(v___x_158_, 2, v_bkt_150_);
v_buckets_x27_159_ = lean_array_uset(v_buckets_133_, v___x_149_, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(4u);
v___x_161_ = lean_nat_mul(v_size_x27_157_, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(3u);
v___x_163_ = lean_nat_div(v___x_161_, v___x_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_array_get_size(v_buckets_x27_159_);
v___x_165_ = lean_nat_dec_le(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
if (v___x_165_ == 0)
{
lean_object* v_val_166_; lean_object* v___x_168_; 
v_val_166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_buckets_x27_159_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_val_166_);
lean_ctor_set(v___x_135_, 0, v_size_x27_157_);
v___x_168_ = v___x_135_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_size_x27_157_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_val_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
else
{
lean_object* v___x_171_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_buckets_x27_159_);
lean_ctor_set(v___x_135_, 0, v_size_x27_157_);
v___x_171_ = v___x_135_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_size_x27_157_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v_buckets_x27_159_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
else
{
lean_object* v___x_173_; lean_object* v_buckets_x27_174_; lean_object* v_bkt_x27_175_; lean_object* v___y_177_; uint8_t v___x_182_; 
lean_inc(v_bkt_150_);
v___x_173_ = lean_box(0);
v_buckets_x27_174_ = lean_array_uset(v_buckets_133_, v___x_149_, v___x_173_);
lean_inc_ref(v_a_131_);
v_bkt_x27_175_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_128_, v_kind_129_, v_a_131_, v_bkt_150_);
v___x_182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_131_, v_bkt_x27_175_);
lean_dec_ref(v_a_131_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_nat_sub(v_size_132_, v___x_183_);
lean_dec(v_size_132_);
v___y_177_ = v___x_184_;
goto v___jp_176_;
}
else
{
v___y_177_ = v_size_132_;
goto v___jp_176_;
}
v___jp_176_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_array_uset(v_buckets_x27_174_, v___x_149_, v_bkt_x27_175_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v___x_178_);
lean_ctor_set(v___x_135_, 0, v___y_177_);
v___x_180_ = v___x_135_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___y_177_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0___boxed(lean_object* v_freshTagId_186_, lean_object* v_kind_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_kind_boxed_190_; lean_object* v_res_191_; 
v_kind_boxed_190_ = lean_unbox(v_kind_187_);
v_res_191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_186_, v_kind_boxed_190_, v_m_188_, v_a_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange(lean_object* v_freshTagId_192_, lean_object* v_tags_193_, lean_object* v_doc_194_, lean_object* v_range_195_, uint8_t v_kind_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v_doc_199_; lean_object* v_tags_200_; lean_object* v___x_201_; lean_object* v_freshTagId_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc_n(v_freshTagId_192_, 2);
v___x_197_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_freshTagId_192_, v_doc_194_);
v___x_198_ = lean_box(0);
v_doc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_doc_199_, 0, v___x_197_);
lean_ctor_set(v_doc_199_, 1, v___x_198_);
v_tags_200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_192_, v_kind_196_, v_tags_193_, v_range_195_);
v___x_201_ = lean_unsigned_to_nat(1u);
v_freshTagId_202_ = lean_nat_add(v_freshTagId_192_, v___x_201_);
lean_dec(v_freshTagId_192_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_tags_200_);
lean_ctor_set(v___x_203_, 1, v_doc_199_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_freshTagId_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange___boxed(lean_object* v_freshTagId_205_, lean_object* v_tags_206_, lean_object* v_doc_207_, lean_object* v_range_208_, lean_object* v_kind_209_){
_start:
{
uint8_t v_kind_boxed_210_; lean_object* v_res_211_; 
v_kind_boxed_210_ = lean_unbox(v_kind_209_);
v_res_211_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_205_, v_tags_206_, v_doc_207_, v_range_208_, v_kind_boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(lean_object* v_00_u03b2_212_, lean_object* v_a_213_, lean_object* v_x_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_213_, v_x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___boxed(lean_object* v_00_u03b2_216_, lean_object* v_a_217_, lean_object* v_x_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(v_00_u03b2_216_, v_a_217_, v_x_218_);
lean_dec(v_x_218_);
lean_dec_ref(v_a_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1(lean_object* v_00_u03b2_221_, lean_object* v_data_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_data_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_224_, lean_object* v_i_225_, lean_object* v_source_226_, lean_object* v_target_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v_i_225_, v_source_226_, v_target_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(v_x_230_, v_x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object* v_doc_233_, lean_object* v_ref_234_, lean_object* v_a_235_){
_start:
{
uint8_t v___x_236_; lean_object* v___x_237_; 
v___x_236_ = 0;
v___x_237_ = l_Lean_Syntax_getRange_x3f(v_ref_234_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 1)
{
lean_object* v_val_238_; lean_object* v_toBacktrackableState_239_; lean_object* v_shareCommonState_240_; lean_object* v_freshTagId_241_; lean_object* v_missingFormatters_242_; lean_object* v_partialFormatters_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_263_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_237_, 1);
v_toBacktrackableState_239_ = lean_ctor_get(v_a_235_, 0);
v_shareCommonState_240_ = lean_ctor_get(v_a_235_, 1);
v_freshTagId_241_ = lean_ctor_get(v_a_235_, 2);
v_missingFormatters_242_ = lean_ctor_get(v_a_235_, 3);
v_partialFormatters_243_ = lean_ctor_get(v_a_235_, 4);
v_isSharedCheck_263_ = !lean_is_exclusive(v_a_235_);
if (v_isSharedCheck_263_ == 0)
{
v___x_245_ = v_a_235_;
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_partialFormatters_243_);
lean_inc(v_missingFormatters_242_);
lean_inc(v_freshTagId_241_);
lean_inc(v_shareCommonState_240_);
lean_inc(v_toBacktrackableState_239_);
lean_dec(v_a_235_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_263_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v_snd_249_; lean_object* v_fst_250_; lean_object* v_fst_251_; lean_object* v_snd_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v___x_247_ = 2;
v___x_248_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_241_, v_toBacktrackableState_239_, v_doc_233_, v_val_238_, v___x_247_);
v_snd_249_ = lean_ctor_get(v___x_248_, 1);
lean_inc(v_snd_249_);
v_fst_250_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_fst_250_);
lean_dec_ref(v___x_248_);
v_fst_251_ = lean_ctor_get(v_snd_249_, 0);
v_snd_252_ = lean_ctor_get(v_snd_249_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_snd_249_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v_snd_249_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_snd_252_);
lean_inc(v_fst_251_);
lean_dec(v_snd_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 2, v_fst_250_);
lean_ctor_set(v___x_245_, 0, v_fst_251_);
v___x_257_ = v___x_245_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_fst_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_shareCommonState_240_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_fst_250_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_missingFormatters_242_);
lean_ctor_set(v_reuseFailAlloc_261_, 4, v_partialFormatters_243_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_257_);
lean_ctor_set(v___x_254_, 0, v_snd_252_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_snd_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v___x_237_);
v___x_264_ = lean_box(0);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v_doc_233_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_a_235_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg___boxed(lean_object* v_doc_267_, lean_object* v_ref_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_267_, v_ref_268_, v_a_269_);
lean_dec(v_ref_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText(lean_object* v_doc_271_, lean_object* v_ref_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_271_, v_ref_272_, v_a_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___boxed(lean_object* v_doc_276_, lean_object* v_ref_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Fmt_TaggedDoc_taggedText(v_doc_276_, v_ref_277_, v_a_278_, v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_ref_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object* v_doc_281_, lean_object* v_ref_282_, lean_object* v_a_283_){
_start:
{
uint8_t v___x_284_; lean_object* v___x_285_; 
v___x_284_ = 0;
v___x_285_ = l_Lean_Syntax_getRange_x3f(v_ref_282_, v___x_284_);
if (lean_obj_tag(v___x_285_) == 1)
{
lean_object* v_val_286_; lean_object* v_toBacktrackableState_287_; lean_object* v_shareCommonState_288_; lean_object* v_freshTagId_289_; lean_object* v_missingFormatters_290_; lean_object* v_partialFormatters_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_311_; 
v_val_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_285_, 1);
v_toBacktrackableState_287_ = lean_ctor_get(v_a_283_, 0);
v_shareCommonState_288_ = lean_ctor_get(v_a_283_, 1);
v_freshTagId_289_ = lean_ctor_get(v_a_283_, 2);
v_missingFormatters_290_ = lean_ctor_get(v_a_283_, 3);
v_partialFormatters_291_ = lean_ctor_get(v_a_283_, 4);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_311_ == 0)
{
v___x_293_ = v_a_283_;
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_partialFormatters_291_);
lean_inc(v_missingFormatters_290_);
lean_inc(v_freshTagId_289_);
lean_inc(v_shareCommonState_288_);
lean_inc(v_toBacktrackableState_287_);
lean_dec(v_a_283_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v_snd_297_; lean_object* v_fst_298_; lean_object* v_fst_299_; lean_object* v_snd_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_310_; 
v___x_295_ = 1;
v___x_296_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_289_, v_toBacktrackableState_287_, v_doc_281_, v_val_286_, v___x_295_);
v_snd_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_snd_297_);
v_fst_298_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_fst_298_);
lean_dec_ref(v___x_296_);
v_fst_299_ = lean_ctor_get(v_snd_297_, 0);
v_snd_300_ = lean_ctor_get(v_snd_297_, 1);
v_isSharedCheck_310_ = !lean_is_exclusive(v_snd_297_);
if (v_isSharedCheck_310_ == 0)
{
v___x_302_ = v_snd_297_;
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snd_300_);
lean_inc(v_fst_299_);
lean_dec(v_snd_297_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_310_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 2, v_fst_298_);
lean_ctor_set(v___x_293_, 0, v_fst_299_);
v___x_305_ = v___x_293_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_fst_299_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_shareCommonState_288_);
lean_ctor_set(v_reuseFailAlloc_309_, 2, v_fst_298_);
lean_ctor_set(v_reuseFailAlloc_309_, 3, v_missingFormatters_290_);
lean_ctor_set(v_reuseFailAlloc_309_, 4, v_partialFormatters_291_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_307_; 
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_305_);
lean_ctor_set(v___x_302_, 0, v_snd_300_);
v___x_307_ = v___x_302_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_snd_300_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v___x_285_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v_doc_281_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_a_283_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg___boxed(lean_object* v_doc_315_, lean_object* v_ref_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_315_, v_ref_316_, v_a_317_);
lean_dec(v_ref_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode(lean_object* v_doc_319_, lean_object* v_ref_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_319_, v_ref_320_, v_a_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___boxed(lean_object* v_doc_324_, lean_object* v_ref_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Fmt_TaggedDoc_taggedNode(v_doc_324_, v_ref_325_, v_a_326_, v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_ref_325_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object* v_doc_329_, lean_object* v_range_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_toBacktrackableState_332_; lean_object* v_shareCommonState_333_; lean_object* v_freshTagId_334_; lean_object* v_missingFormatters_335_; lean_object* v_partialFormatters_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_356_; 
v_toBacktrackableState_332_ = lean_ctor_get(v_a_331_, 0);
v_shareCommonState_333_ = lean_ctor_get(v_a_331_, 1);
v_freshTagId_334_ = lean_ctor_get(v_a_331_, 2);
v_missingFormatters_335_ = lean_ctor_get(v_a_331_, 3);
v_partialFormatters_336_ = lean_ctor_get(v_a_331_, 4);
v_isSharedCheck_356_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_356_ == 0)
{
v___x_338_ = v_a_331_;
v_isShared_339_ = v_isSharedCheck_356_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_partialFormatters_336_);
lean_inc(v_missingFormatters_335_);
lean_inc(v_freshTagId_334_);
lean_inc(v_shareCommonState_333_);
lean_inc(v_toBacktrackableState_332_);
lean_dec(v_a_331_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_356_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v_snd_342_; lean_object* v_fst_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_355_; 
v___x_340_ = 0;
v___x_341_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_334_, v_toBacktrackableState_332_, v_doc_329_, v_range_330_, v___x_340_);
v_snd_342_ = lean_ctor_get(v___x_341_, 1);
lean_inc(v_snd_342_);
v_fst_343_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_fst_343_);
lean_dec_ref(v___x_341_);
v_fst_344_ = lean_ctor_get(v_snd_342_, 0);
v_snd_345_ = lean_ctor_get(v_snd_342_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_snd_342_);
if (v_isSharedCheck_355_ == 0)
{
v___x_347_ = v_snd_342_;
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snd_345_);
lean_inc(v_fst_344_);
lean_dec(v_snd_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 2, v_fst_343_);
lean_ctor_set(v___x_338_, 0, v_fst_344_);
v___x_350_ = v___x_338_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_fst_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v_shareCommonState_333_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_fst_343_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_missingFormatters_335_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_partialFormatters_336_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_350_);
lean_ctor_set(v___x_347_, 0, v_snd_345_);
v___x_352_ = v___x_347_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_snd_345_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace(lean_object* v_doc_357_, lean_object* v_range_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_357_, v_range_358_, v_a_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___boxed(lean_object* v_doc_362_, lean_object* v_range_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace(v_doc_362_, v_range_363_, v_a_364_, v_a_365_);
lean_dec_ref(v_a_364_);
return v_res_366_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isTagged(lean_object* v_d_367_){
_start:
{
lean_object* v_doc_368_; 
v_doc_368_ = lean_ctor_get(v_d_367_, 0);
if (lean_obj_tag(v_doc_368_) == 3)
{
uint8_t v___x_369_; 
v___x_369_ = 1;
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isTagged___boxed(lean_object* v_d_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_371_);
lean_dec_ref(v_d_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object* v_d_374_, lean_object* v_ref_375_, lean_object* v_a_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_374_);
if (v___x_377_ == 0)
{
lean_object* v_doc_378_; lean_object* v_metaData_379_; lean_object* v___x_380_; lean_object* v_a_381_; lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_398_; 
v_doc_378_ = lean_ctor_get(v_d_374_, 0);
lean_inc(v_doc_378_);
v_metaData_379_ = lean_ctor_get(v_d_374_, 1);
lean_inc(v_metaData_379_);
lean_dec_ref(v_d_374_);
v___x_380_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_378_, v_ref_375_, v_a_376_);
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_a_382_ = lean_ctor_get(v___x_380_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_398_ == 0)
{
v___x_384_ = v___x_380_;
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_doc_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_396_; 
v_doc_386_ = lean_ctor_get(v_a_381_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_a_381_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_a_381_, 1);
lean_dec(v_unused_397_);
v___x_388_ = v_a_381_;
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_doc_386_);
lean_dec(v_a_381_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_396_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v_metaData_379_);
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_doc_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_metaData_379_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_393_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_391_);
v___x_393_ = v___x_384_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_a_382_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_d_374_);
lean_ctor_set(v___x_399_, 1, v_a_376_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg___boxed(lean_object* v_d_400_, lean_object* v_ref_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_400_, v_ref_401_, v_a_402_);
lean_dec(v_ref_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag(lean_object* v_d_404_, lean_object* v_ref_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_404_, v_ref_405_, v_a_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___boxed(lean_object* v_d_409_, lean_object* v_ref_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Fmt_TaggedDoc_tag(v_d_409_, v_ref_410_, v_a_411_, v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_ref_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(lean_object* v_inst_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_v_416_; lean_object* v___x_417_; 
v_v_416_ = lean_ctor_get(v_x_415_, 0);
v___x_417_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_416_, v_inst_414_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed(lean_object* v_inst_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(v_inst_418_, v_x_419_);
lean_dec_ref(v_x_419_);
lean_dec(v_inst_418_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(lean_object* v_inst_421_, lean_object* v_d_422_){
_start:
{
lean_object* v_metaData_423_; lean_object* v___f_424_; lean_object* v___x_425_; 
v_metaData_423_ = lean_ctor_get(v_d_422_, 1);
lean_inc(v_metaData_423_);
lean_dec_ref(v_d_422_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_424_, 0, v_inst_421_);
v___x_425_ = l_List_findSome_x3f___redArg(v___f_424_, v_metaData_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f(lean_object* v_00_u03b1_426_, lean_object* v_inst_427_, lean_object* v_d_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v_inst_427_, v_d_428_);
return v___x_429_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_433_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2));
v___x_434_ = lean_unsigned_to_nat(14u);
v___x_435_ = lean_unsigned_to_nat(22u);
v___x_436_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1));
v___x_437_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0));
v___x_438_ = l_mkPanicMessageWithDecl(v___x_437_, v___x_436_, v___x_435_, v___x_434_, v___x_433_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_propagate_441_, lean_object* v_v_442_, lean_object* v_f_443_){
_start:
{
lean_object* v___y_445_; lean_object* v___x_448_; 
v___x_448_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_442_, v_inst_440_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3);
v___x_450_ = l_panic___redArg(v_inst_439_, v___x_449_);
v___y_445_ = v___x_450_;
goto v___jp_444_;
}
else
{
lean_object* v_val_451_; 
v_val_451_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_val_451_);
lean_dec_ref_known(v___x_448_, 1);
v___y_445_ = v_val_451_;
goto v___jp_444_;
}
v___jp_444_:
{
lean_object* v_r_446_; lean_object* v___x_447_; 
v_r_446_ = lean_apply_2(v_propagate_441_, v___y_445_, v_f_443_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v_inst_440_);
lean_ctor_set(v___x_447_, 1, v_r_446_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___boxed(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_propagate_454_, lean_object* v_v_455_, lean_object* v_f_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_452_, v_inst_453_, v_propagate_454_, v_v_455_, v_f_456_);
lean_dec(v_v_455_);
lean_dec(v_inst_452_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(lean_object* v_00_u03b1_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_propagate_461_, lean_object* v_v_462_, lean_object* v_f_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_459_, v_inst_460_, v_propagate_461_, v_v_462_, v_f_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed(lean_object* v_00_u03b1_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_propagate_468_, lean_object* v_v_469_, lean_object* v_f_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(v_00_u03b1_465_, v_inst_466_, v_inst_467_, v_propagate_468_, v_v_469_, v_f_470_);
lean_dec(v_v_469_);
lean_dec(v_inst_466_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData___redArg(lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_d_474_, lean_object* v_metaData_475_, lean_object* v_propagate_476_){
_start:
{
lean_object* v_doc_477_; lean_object* v_metaData_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v_doc_477_ = lean_ctor_get(v_d_474_, 0);
v_metaData_478_ = lean_ctor_get(v_d_474_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_d_474_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v_d_474_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_metaData_478_);
lean_inc(v_doc_477_);
lean_dec(v_d_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
lean_inc(v_inst_473_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v_inst_473_);
lean_ctor_set(v___x_482_, 1, v_metaData_475_);
v___x_483_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed), 6, 4);
lean_closure_set(v___x_483_, 0, lean_box(0));
lean_closure_set(v___x_483_, 1, v_inst_472_);
lean_closure_set(v___x_483_, 2, v_inst_473_);
lean_closure_set(v___x_483_, 3, v_propagate_476_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
v___x_485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_metaData_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_485_);
v___x_487_ = v___x_480_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_doc_477_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_d_493_, lean_object* v_metaData_494_, lean_object* v_propagate_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v_inst_491_, v_inst_492_, v_d_493_, v_metaData_494_, v_propagate_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(lean_object* v_f_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
if (lean_obj_tag(v_a_498_) == 0)
{
lean_object* v___x_500_; 
lean_dec_ref(v_f_497_);
v___x_500_ = l_List_reverse___redArg(v_a_499_);
return v___x_500_;
}
else
{
lean_object* v_head_501_; lean_object* v_tail_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_520_; 
v_head_501_ = lean_ctor_get(v_a_498_, 0);
v_tail_502_ = lean_ctor_get(v_a_498_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_a_498_);
if (v_isSharedCheck_520_ == 0)
{
v___x_504_ = v_a_498_;
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_tail_502_);
lean_inc(v_head_501_);
lean_dec(v_a_498_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_520_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_v_506_; lean_object* v_propagate_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_v_506_ = lean_ctor_get(v_head_501_, 0);
v_propagate_507_ = lean_ctor_get(v_head_501_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_head_501_);
if (v_isSharedCheck_519_ == 0)
{
v___x_509_ = v_head_501_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_propagate_507_);
lean_inc(v_v_506_);
lean_dec(v_head_501_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
lean_inc(v_propagate_507_);
lean_inc_ref(v_f_497_);
v___x_511_ = lean_apply_2(v_propagate_507_, v_v_506_, v_f_497_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_propagate_507_);
v___x_513_ = v_reuseFailAlloc_518_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v_a_499_);
lean_ctor_set(v___x_504_, 0, v___x_513_);
v___x_515_ = v___x_504_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_a_499_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v_a_498_ = v_tail_502_;
v_a_499_ = v___x_515_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateMetaData(lean_object* v_d_521_, lean_object* v_f_522_){
_start:
{
lean_object* v_doc_523_; lean_object* v_metaData_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_534_; 
v_doc_523_ = lean_ctor_get(v_d_521_, 0);
v_metaData_524_ = lean_ctor_get(v_d_521_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_d_521_);
if (v_isSharedCheck_534_ == 0)
{
v___x_526_ = v_d_521_;
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_metaData_524_);
lean_inc(v_doc_523_);
lean_dec(v_d_521_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
lean_inc_ref(v_f_522_);
v___x_528_ = lean_apply_1(v_f_522_, v_doc_523_);
v___x_529_ = lean_box(0);
v___x_530_ = l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(v_f_522_, v_metaData_524_, v___x_529_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_530_);
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(size_t v_sz_535_, size_t v_i_536_, lean_object* v_bs_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_536_, v_sz_535_);
if (v___x_538_ == 0)
{
return v_bs_537_;
}
else
{
lean_object* v_v_539_; lean_object* v_doc_540_; lean_object* v___x_541_; lean_object* v_bs_x27_542_; size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; 
v_v_539_ = lean_array_uget_borrowed(v_bs_537_, v_i_536_);
v_doc_540_ = lean_ctor_get(v_v_539_, 0);
lean_inc(v_doc_540_);
v___x_541_ = lean_unsigned_to_nat(0u);
v_bs_x27_542_ = lean_array_uset(v_bs_537_, v_i_536_, v___x_541_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_536_, v___x_543_);
v___x_545_ = lean_array_uset(v_bs_x27_542_, v_i_536_, v_doc_540_);
v_i_536_ = v___x_544_;
v_bs_537_ = v___x_545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0___boxed(lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_bs_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_551_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_boxed_550_, v_i_boxed_551_, v_bs_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(lean_object* v_ds_553_, lean_object* v_f_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_array_get_size(v_ds_553_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
size_t v_sz_558_; size_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_sz_558_ = lean_array_size(v_ds_553_);
v___x_559_ = ((size_t)0ULL);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_558_, v___x_559_, v_ds_553_);
v___x_561_ = lean_apply_1(v_f_554_, v___x_560_);
v___x_562_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_561_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_dec_ref(v_f_554_);
v___x_563_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_array_get(v___x_563_, v_ds_553_, v___x_564_);
lean_dec_ref(v_ds_553_);
return v___x_565_;
}
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure___closed__0(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_box(0);
v___x_567_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure(void){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_failure___closed__0, &l_Lean_Fmt_TaggedDoc_failure___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_failure___closed__0);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_newline(lean_object* v_flattened_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = l_Lean_Fmt_Doc_newline___override___redArg(v_flattened_569_);
v___x_571_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__0(void){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Fmt_Doc_nl___redArg();
return v___x_572_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__0, &l_Lean_Fmt_TaggedDoc_nl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__0);
v___x_574_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__1, &l_Lean_Fmt_TaggedDoc_nl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__1);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__0(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Fmt_Doc_break___redArg();
return v___x_576_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__0, &l_Lean_Fmt_TaggedDoc_break___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__0);
v___x_578_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__1, &l_Lean_Fmt_TaggedDoc_break___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__1);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__0, &l_Lean_Fmt_TaggedDoc_hardNl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0);
v___x_582_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl(void){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__1, &l_Lean_Fmt_TaggedDoc_hardNl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object* v_s_584_, lean_object* v_ref_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_584_);
v___x_588_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_587_, v_ref_585_, v_a_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg___boxed(lean_object* v_s_589_, lean_object* v_ref_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_589_, v_ref_590_, v_a_591_);
lean_dec(v_ref_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text(lean_object* v_s_593_, lean_object* v_ref_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_593_, v_ref_594_, v_a_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___boxed(lean_object* v_s_598_, lean_object* v_ref_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Fmt_TaggedDoc_text(v_s_598_, v_ref_599_, v_a_600_, v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_ref_599_);
return v_res_602_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__0(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Fmt_Doc_empty___redArg();
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__0, &l_Lean_Fmt_TaggedDoc_empty___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__0);
v___x_605_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty(void){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__1, &l_Lean_Fmt_TaggedDoc_empty___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__1);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_space___closed__0));
v___x_609_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__2(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__1, &l_Lean_Fmt_TaggedDoc_space___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__1);
v___x_611_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__2, &l_Lean_Fmt_TaggedDoc_space___closed__2_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__2);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object* v_d_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_nested___closed__0));
v___x_616_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_614_, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object* v_d_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_hardNested___closed__0));
v___x_620_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_618_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_doublyNested(lean_object* v_d_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = l_Lean_Fmt_TaggedDoc_nested(v_d_621_);
v___x_623_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object* v_d_624_){
_start:
{
lean_object* v_doc_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_doc_625_ = lean_ctor_get(v_d_624_, 0);
lean_inc(v_doc_625_);
lean_dec_ref(v_d_624_);
v___x_626_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_625_);
v___x_627_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object* v_d_629_){
_start:
{
lean_object* v___f_630_; lean_object* v___x_631_; 
v___f_630_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_unflattenable___closed__0));
v___x_631_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_629_, v___f_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object* v_d_633_){
_start:
{
lean_object* v___f_634_; lean_object* v___x_635_; 
v___f_634_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_flattened___closed__0));
v___x_635_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_633_, v___f_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object* v_d_637_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0));
v___x_639_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_637_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0(uint8_t v_onlyNonCumulative_640_, lean_object* v_d_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_640_, v_d_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed(lean_object* v_onlyNonCumulative_643_, lean_object* v_d_644_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_645_; lean_object* v_res_646_; 
v_onlyNonCumulative_boxed_645_ = lean_unbox(v_onlyNonCumulative_643_);
v_res_646_ = l_Lean_Fmt_TaggedDoc_unindented___lam__0(v_onlyNonCumulative_boxed_645_, v_d_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object* v_d_647_, uint8_t v_onlyNonCumulative_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; 
v___x_649_ = lean_box(v_onlyNonCumulative_648_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed), 2, 1);
lean_closure_set(v___f_650_, 0, v___x_649_);
v___x_651_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_647_, v___f_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___boxed(lean_object* v_d_652_, lean_object* v_onlyNonCumulative_653_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_654_; lean_object* v_res_655_; 
v_onlyNonCumulative_boxed_654_ = lean_unbox(v_onlyNonCumulative_653_);
v_res_655_ = l_Lean_Fmt_TaggedDoc_unindented(v_d_652_, v_onlyNonCumulative_boxed_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_final(lean_object* v_d_657_){
_start:
{
lean_object* v___f_658_; lean_object* v___x_659_; 
v___f_658_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_final___closed__0));
v___x_659_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_657_, v___f_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_initial(lean_object* v_d_661_){
_start:
{
lean_object* v___f_662_; lean_object* v___x_663_; 
v___f_662_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_initial___closed__0));
v___x_663_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_661_, v___f_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object* v_d_665_){
_start:
{
lean_object* v___f_666_; lean_object* v___x_667_; 
v___f_666_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_free___closed__0));
v___x_667_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_665_, v___f_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded___lam__0(lean_object* v_p_668_, lean_object* v_d_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_668_, v_d_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object* v_p_671_, lean_object* v_d_672_){
_start:
{
lean_object* v___f_673_; lean_object* v___x_674_; 
v___f_673_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_guarded___lam__0), 2, 1);
lean_closure_set(v___f_673_, 0, v_p_671_);
v___x_674_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_672_, v___f_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0(lean_object* v_amount_675_, lean_object* v_d_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = l_Lean_Fmt_DefaultCost_ofFailureFallbackPenalty___redArg(v_amount_675_);
v___x_678_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_677_, v_d_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(lean_object* v_d_679_, lean_object* v_amount_680_){
_start:
{
lean_object* v___f_681_; lean_object* v___x_682_; 
v___f_681_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_681_, 0, v_amount_680_);
v___x_682_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_679_, v___f_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0(lean_object* v_amount_683_, lean_object* v_d_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_Lean_Fmt_DefaultCost_ofOverflowFallbackPenalty___redArg(v_amount_683_);
v___x_686_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_685_, v_d_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(lean_object* v_d_687_, lean_object* v_amount_688_){
_start:
{
lean_object* v___f_689_; lean_object* v___x_690_; 
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_689_, 0, v_amount_688_);
v___x_690_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_687_, v___f_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0(lean_object* v_amount_691_, lean_object* v_d_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v_amount_691_);
v___x_694_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_693_, v_d_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(lean_object* v_d_695_, lean_object* v_amount_696_){
_start:
{
lean_object* v___f_697_; lean_object* v___x_698_; 
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_697_, 0, v_amount_696_);
v___x_698_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_695_, v___f_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_either(lean_object* v_a_699_, lean_object* v_b_700_){
_start:
{
lean_object* v_doc_701_; lean_object* v_doc_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_doc_701_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_doc_701_);
lean_dec_ref(v_a_699_);
v_doc_702_ = lean_ctor_get(v_b_700_, 0);
lean_inc(v_doc_702_);
lean_dec_ref(v_b_700_);
v___x_703_ = l_Lean_Fmt_Doc_either___override___redArg(v_doc_701_, v_doc_702_);
v___x_704_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object* v_ds_706_){
_start:
{
lean_object* v___f_707_; lean_object* v___x_708_; 
v___f_707_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_oneOf___closed__0));
v___x_708_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_706_, v___f_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnFailure(lean_object* v_d_709_, lean_object* v_fallback_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_711_ = lean_unsigned_to_nat(1u);
v___x_712_ = l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(v_fallback_710_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(2u);
v___x_714_ = lean_mk_empty_array_with_capacity(v___x_713_);
v___x_715_ = lean_array_push(v___x_714_, v_d_709_);
v___x_716_ = lean_array_push(v___x_715_, v___x_712_);
v___x_717_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object* v_d_718_, lean_object* v_fallback_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_fallback_719_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(2u);
v___x_723_ = lean_mk_empty_array_with_capacity(v___x_722_);
v___x_724_ = lean_array_push(v___x_723_, v_d_718_);
v___x_725_ = lean_array_push(v___x_724_, v___x_721_);
v___x_726_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object* v_d_727_, lean_object* v_fallback_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_729_ = lean_unsigned_to_nat(1u);
v___x_730_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v_fallback_728_, v___x_729_);
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = lean_mk_empty_array_with_capacity(v___x_731_);
v___x_733_ = lean_array_push(v___x_732_, v_d_727_);
v___x_734_ = lean_array_push(v___x_733_, v___x_730_);
v___x_735_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_737_ = l_Lean_Fmt_TaggedDoc_space;
v___x_738_ = l_Lean_Fmt_TaggedDoc_fallbackOnFailure(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace(void){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_softSpace___closed__0, &l_Lean_Fmt_TaggedDoc_softSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object* v_a_740_, lean_object* v_b_741_){
_start:
{
lean_object* v_doc_742_; lean_object* v_doc_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_doc_742_ = lean_ctor_get(v_a_740_, 0);
lean_inc(v_doc_742_);
lean_dec_ref(v_a_740_);
v_doc_743_ = lean_ctor_get(v_b_741_, 0);
lean_inc(v_doc_743_);
lean_dec_ref(v_b_741_);
v___x_744_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_742_, v_doc_743_);
v___x_745_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object* v_ds_747_){
_start:
{
lean_object* v___f_748_; lean_object* v___x_749_; 
v___f_748_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_join___closed__0));
v___x_749_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_747_, v___f_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing___lam__0(lean_object* v_sep_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_doc_752_; lean_object* v___x_753_; 
v_doc_752_ = lean_ctor_get(v_sep_750_, 0);
lean_inc(v_doc_752_);
lean_dec_ref(v_sep_750_);
v___x_753_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_doc_752_, v_x_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object* v_sep_754_, lean_object* v_ds_755_){
_start:
{
lean_object* v___f_756_; lean_object* v___x_757_; 
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_joinUsing___lam__0), 2, 1);
lean_closure_set(v___f_756_, 0, v_sep_754_);
v___x_757_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_755_, v___f_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object* v_ds_759_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_761_; 
v___f_760_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fill___closed__0));
v___x_761_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_759_, v___f_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0(lean_object* v_wrap_762_, lean_object* v_d_763_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_doc_766_; 
v___x_764_ = l_Lean_Fmt_TaggedDoc_untagged(v_d_763_);
v___x_765_ = lean_apply_1(v_wrap_762_, v___x_764_);
v_doc_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_doc_766_);
lean_dec_ref(v___x_765_);
return v_doc_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1(lean_object* v___f_767_, lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_x_768_, v___f_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object* v_ds_770_, lean_object* v_wrap_771_){
_start:
{
lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___x_774_; 
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_772_, 0, v_wrap_771_);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1), 2, 1);
lean_closure_set(v___f_773_, 0, v___f_772_);
v___x_774_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_770_, v___f_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing___lam__0(lean_object* v_sep_775_, lean_object* v_x_776_){
_start:
{
lean_object* v_doc_777_; lean_object* v___x_778_; 
v_doc_777_ = lean_ctor_get(v_sep_775_, 0);
lean_inc(v_doc_777_);
lean_dec_ref(v_sep_775_);
v___x_778_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_doc_777_, v_x_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing(lean_object* v_sep_779_, lean_object* v_ds_780_){
_start:
{
lean_object* v___f_781_; lean_object* v___x_782_; 
v___f_781_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsing___lam__0), 2, 1);
lean_closure_set(v___f_781_, 0, v_sep_779_);
v___x_782_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_780_, v___f_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object* v_ds_784_){
_start:
{
lean_object* v___f_785_; lean_object* v___x_786_; 
v___f_785_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0));
v___x_786_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_784_, v___f_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1(lean_object* v___f_787_, lean_object* v_x_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_x_788_, v___f_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object* v_ds_790_, lean_object* v_wrap_791_){
_start:
{
lean_object* v___f_792_; lean_object* v___f_793_; lean_object* v___x_794_; 
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_792_, 0, v_wrap_791_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1), 2, 1);
lean_closure_set(v___f_793_, 0, v___f_792_);
v___x_794_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_790_, v___f_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_as_795_, size_t v_i_796_, size_t v_stop_797_, lean_object* v_b_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_eq(v_i_796_, v_stop_797_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; size_t v___x_802_; size_t v___x_803_; 
v___x_800_ = lean_array_uget_borrowed(v_as_795_, v_i_796_);
v___x_801_ = l_Array_append___redArg(v_b_798_, v___x_800_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_796_, v___x_802_);
v_i_796_ = v___x_803_;
v_b_798_ = v___x_801_;
goto _start;
}
else
{
return v_b_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object* v_as_805_, lean_object* v_i_806_, lean_object* v_stop_807_, lean_object* v_b_808_){
_start:
{
size_t v_i_boxed_809_; size_t v_stop_boxed_810_; lean_object* v_res_811_; 
v_i_boxed_809_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_stop_boxed_810_ = lean_unbox_usize(v_stop_807_);
lean_dec(v_stop_807_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_as_805_, v_i_boxed_809_, v_stop_boxed_810_, v_b_808_);
lean_dec_ref(v_as_805_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(size_t v_sz_812_, size_t v_i_813_, lean_object* v_bs_814_){
_start:
{
uint8_t v___x_815_; 
v___x_815_ = lean_usize_dec_lt(v_i_813_, v_sz_812_);
if (v___x_815_ == 0)
{
return v_bs_814_;
}
else
{
lean_object* v_v_816_; lean_object* v___x_817_; lean_object* v_bs_x27_818_; size_t v_sz_819_; size_t v___x_820_; lean_object* v___x_821_; size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v_v_816_ = lean_array_uget(v_bs_814_, v_i_813_);
v___x_817_ = lean_unsigned_to_nat(0u);
v_bs_x27_818_ = lean_array_uset(v_bs_814_, v_i_813_, v___x_817_);
v_sz_819_ = lean_array_size(v_v_816_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_819_, v___x_820_, v_v_816_);
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_813_, v___x_822_);
v___x_824_ = lean_array_uset(v_bs_x27_818_, v_i_813_, v___x_821_);
v_i_813_ = v___x_823_;
v_bs_814_ = v___x_824_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_bs_828_){
_start:
{
size_t v_sz_boxed_829_; size_t v_i_boxed_830_; lean_object* v_res_831_; 
v_sz_boxed_829_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_830_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_boxed_829_, v_i_boxed_830_, v_bs_828_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object* v_dss_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___y_839_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_837_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1));
v___x_853_ = lean_array_get_size(v_dss_836_);
v___x_854_ = lean_nat_dec_lt(v___x_851_, v___x_853_);
if (v___x_854_ == 0)
{
v___y_839_ = v___x_852_;
goto v___jp_838_;
}
else
{
size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((size_t)0ULL);
v___x_856_ = lean_usize_of_nat(v___x_853_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_dss_836_, v___x_855_, v___x_856_, v___x_852_);
v___y_839_ = v___x_857_;
goto v___jp_838_;
}
v___jp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_840_ = lean_array_get_size(v___y_839_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_dec_eq(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; size_t v_sz_844_; size_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v___y_839_);
v___x_843_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0, &l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0);
v_sz_844_ = lean_array_size(v_dss_836_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_844_, v___x_845_, v_dss_836_);
v___x_847_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v___x_843_, v___x_846_);
lean_dec_ref(v___x_846_);
v___x_848_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_847_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec_ref(v_dss_836_);
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_array_get(v___x_837_, v___y_839_, v___x_849_);
lean_dec_ref(v___y_839_);
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(size_t v_sz_858_, size_t v_i_859_, lean_object* v_bs_860_){
_start:
{
uint8_t v___x_861_; 
v___x_861_ = lean_usize_dec_lt(v_i_859_, v_sz_858_);
if (v___x_861_ == 0)
{
return v_bs_860_;
}
else
{
lean_object* v_v_862_; lean_object* v_v_863_; uint8_t v_allowFill_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_878_; 
v_v_862_ = lean_array_uget(v_bs_860_, v_i_859_);
v_v_863_ = lean_ctor_get(v_v_862_, 0);
v_allowFill_864_ = lean_ctor_get_uint8(v_v_862_, sizeof(void*)*1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_v_862_);
if (v_isSharedCheck_878_ == 0)
{
v___x_866_ = v_v_862_;
v_isShared_867_ = v_isSharedCheck_878_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_v_863_);
lean_dec(v_v_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_878_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_doc_868_; lean_object* v___x_869_; lean_object* v_bs_x27_870_; lean_object* v___x_872_; 
v_doc_868_ = lean_ctor_get(v_v_863_, 0);
lean_inc(v_doc_868_);
lean_dec(v_v_863_);
v___x_869_ = lean_unsigned_to_nat(0u);
v_bs_x27_870_ = lean_array_uset(v_bs_860_, v_i_859_, v___x_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_doc_868_);
v___x_872_ = v___x_866_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_doc_868_);
lean_ctor_set_uint8(v_reuseFailAlloc_877_, sizeof(void*)*1, v_allowFill_864_);
v___x_872_ = v_reuseFailAlloc_877_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_859_, v___x_873_);
v___x_875_ = lean_array_uset(v_bs_x27_870_, v_i_859_, v___x_872_);
v_i_859_ = v___x_874_;
v_bs_860_ = v___x_875_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0___boxed(lean_object* v_sz_879_, lean_object* v_i_880_, lean_object* v_bs_881_){
_start:
{
size_t v_sz_boxed_882_; size_t v_i_boxed_883_; lean_object* v_res_884_; 
v_sz_boxed_882_ = lean_unbox_usize(v_sz_879_);
lean_dec(v_sz_879_);
v_i_boxed_883_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_boxed_882_, v_i_boxed_883_, v_bs_881_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_886_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsing(lean_object* v_sep_887_, lean_object* v_ds_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_889_ = lean_array_get_size(v_ds_888_);
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_nat_dec_eq(v___x_889_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v_doc_892_; size_t v_sz_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_doc_892_ = lean_ctor_get(v_sep_887_, 0);
lean_inc(v_doc_892_);
lean_dec_ref(v_sep_887_);
v_sz_893_ = lean_array_size(v_ds_888_);
v___x_894_ = ((size_t)0ULL);
v___x_895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_893_, v___x_894_, v_ds_888_);
v___x_896_ = l_Lean_Fmt_Doc_fillSomeUsing___redArg(v_doc_892_, v___x_895_);
v___x_897_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_896_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v_v_901_; 
lean_dec_ref(v_sep_887_);
v___x_898_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_array_get(v___x_898_, v_ds_888_, v___x_899_);
lean_dec_ref(v_ds_888_);
v_v_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_v_901_);
lean_dec(v___x_900_);
return v_v_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object* v_ds_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = lean_array_get_size(v_ds_902_);
v___x_904_ = lean_unsigned_to_nat(1u);
v___x_905_ = lean_nat_dec_eq(v___x_903_, v___x_904_);
if (v___x_905_ == 0)
{
size_t v_sz_906_; size_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_sz_906_ = lean_array_size(v_ds_902_);
v___x_907_ = ((size_t)0ULL);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_906_, v___x_907_, v_ds_902_);
v___x_909_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v___x_908_);
v___x_910_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_909_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_v_914_; 
v___x_911_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_array_get(v___x_911_, v_ds_902_, v___x_912_);
lean_dec_ref(v_ds_902_);
v_v_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_v_914_);
lean_dec(v___x_913_);
return v_v_914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object* v_ds_915_, lean_object* v_wrap_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = lean_array_get_size(v_ds_915_);
v___x_918_ = lean_unsigned_to_nat(1u);
v___x_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
lean_object* v___f_920_; size_t v_sz_921_; size_t v___x_922_; lean_object* v_ds_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_920_, 0, v_wrap_916_);
v_sz_921_ = lean_array_size(v_ds_915_);
v___x_922_ = ((size_t)0ULL);
v_ds_923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_921_, v___x_922_, v_ds_915_);
v___x_924_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_923_, v___f_920_);
v___x_925_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_924_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_v_929_; 
lean_dec_ref(v_wrap_916_);
v___x_926_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_array_get(v___x_926_, v_ds_915_, v___x_927_);
lean_dec_ref(v_ds_915_);
v_v_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_v_929_);
lean_dec(v___x_928_);
return v_v_929_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object* v_d_930_){
_start:
{
lean_object* v_doc_931_; uint8_t v___x_932_; 
v_doc_931_ = lean_ctor_get(v_d_930_, 0);
v___x_932_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object* v_d_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_d_933_);
lean_dec_ref(v_d_933_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(lean_object* v_d_936_){
_start:
{
lean_object* v_doc_937_; uint8_t v___x_938_; 
v_doc_937_ = lean_ctor_get(v_d_936_, 0);
v___x_938_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_doc_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty___boxed(lean_object* v_d_939_){
_start:
{
uint8_t v_res_940_; lean_object* v_r_941_; 
v_res_940_ = l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(v_d_939_);
lean_dec_ref(v_d_939_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isCompoundAtomic(lean_object* v_d_942_){
_start:
{
lean_object* v_doc_943_; uint8_t v___x_944_; 
v_doc_943_ = lean_ctor_get(v_d_942_, 0);
v___x_944_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_doc_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isCompoundAtomic___boxed(lean_object* v_d_945_){
_start:
{
uint8_t v_res_946_; lean_object* v_r_947_; 
v_res_946_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_d_945_);
lean_dec_ref(v_d_945_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object* v_d_948_){
_start:
{
lean_object* v_doc_949_; uint8_t v___x_950_; 
v_doc_949_ = lean_ctor_get(v_d_948_, 0);
v___x_950_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_doc_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAtomic___boxed(lean_object* v_d_951_){
_start:
{
uint8_t v_res_952_; lean_object* v_r_953_; 
v_res_952_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_d_951_);
lean_dec_ref(v_d_951_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instAppend___lam__0(lean_object* v_a_954_, lean_object* v_b_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_954_);
if (v___x_956_ == 0)
{
uint8_t v___x_957_; 
v___x_957_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_955_);
if (v___x_957_ == 0)
{
lean_object* v_doc_958_; lean_object* v_doc_959_; uint8_t v___x_960_; 
v_doc_958_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_doc_958_);
lean_dec_ref(v_a_954_);
v_doc_959_ = lean_ctor_get(v_b_955_, 0);
lean_inc(v_doc_959_);
lean_dec_ref(v_b_955_);
v___x_960_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_958_);
if (v___x_960_ == 0)
{
uint8_t v___x_961_; 
v___x_961_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_959_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_958_, v_doc_959_);
v___x_963_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_962_);
return v___x_963_;
}
else
{
lean_object* v___x_964_; 
lean_dec(v_doc_959_);
v___x_964_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_958_);
return v___x_964_;
}
}
else
{
lean_object* v___x_965_; 
lean_dec(v_doc_958_);
v___x_965_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_959_);
return v___x_965_;
}
}
else
{
lean_dec_ref(v_b_955_);
return v_a_954_;
}
}
else
{
lean_dec_ref(v_a_954_);
return v_b_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(uint8_t v_x_968_){
_start:
{
switch(v_x_968_)
{
case 0:
{
lean_object* v___x_969_; 
v___x_969_ = lean_unsigned_to_nat(0u);
return v___x_969_;
}
case 1:
{
lean_object* v___x_970_; 
v___x_970_ = lean_unsigned_to_nat(1u);
return v___x_970_;
}
default: 
{
lean_object* v___x_971_; 
v___x_971_ = lean_unsigned_to_nat(2u);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___boxed(lean_object* v_x_972_){
_start:
{
uint8_t v_x_boxed_973_; lean_object* v_res_974_; 
v_x_boxed_973_ = lean_unbox(v_x_972_);
v_res_974_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_x_boxed_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(lean_object* v_k_975_){
_start:
{
lean_inc(v_k_975_);
return v_k_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg___boxed(lean_object* v_k_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(v_k_976_);
lean_dec(v_k_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(lean_object* v_motive_978_, lean_object* v_ctorIdx_979_, uint8_t v_t_980_, lean_object* v_h_981_, lean_object* v_k_982_){
_start:
{
lean_inc(v_k_982_);
return v_k_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___boxed(lean_object* v_motive_983_, lean_object* v_ctorIdx_984_, lean_object* v_t_985_, lean_object* v_h_986_, lean_object* v_k_987_){
_start:
{
uint8_t v_t_boxed_988_; lean_object* v_res_989_; 
v_t_boxed_988_ = lean_unbox(v_t_985_);
v_res_989_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(v_motive_983_, v_ctorIdx_984_, v_t_boxed_988_, v_h_986_, v_k_987_);
lean_dec(v_k_987_);
lean_dec(v_ctorIdx_984_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(lean_object* v_coequal_990_){
_start:
{
lean_inc(v_coequal_990_);
return v_coequal_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg___boxed(lean_object* v_coequal_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(v_coequal_991_);
lean_dec(v_coequal_991_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(lean_object* v_motive_993_, uint8_t v_t_994_, lean_object* v_h_995_, lean_object* v_coequal_996_){
_start:
{
lean_inc(v_coequal_996_);
return v_coequal_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___boxed(lean_object* v_motive_997_, lean_object* v_t_998_, lean_object* v_h_999_, lean_object* v_coequal_1000_){
_start:
{
uint8_t v_t_boxed_1001_; lean_object* v_res_1002_; 
v_t_boxed_1001_ = lean_unbox(v_t_998_);
v_res_1002_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(v_motive_997_, v_t_boxed_1001_, v_h_999_, v_coequal_1000_);
lean_dec(v_coequal_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(lean_object* v_preferSticky_1003_){
_start:
{
lean_inc(v_preferSticky_1003_);
return v_preferSticky_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg___boxed(lean_object* v_preferSticky_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(v_preferSticky_1004_);
lean_dec(v_preferSticky_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(lean_object* v_motive_1006_, uint8_t v_t_1007_, lean_object* v_h_1008_, lean_object* v_preferSticky_1009_){
_start:
{
lean_inc(v_preferSticky_1009_);
return v_preferSticky_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___boxed(lean_object* v_motive_1010_, lean_object* v_t_1011_, lean_object* v_h_1012_, lean_object* v_preferSticky_1013_){
_start:
{
uint8_t v_t_boxed_1014_; lean_object* v_res_1015_; 
v_t_boxed_1014_ = lean_unbox(v_t_1011_);
v_res_1015_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(v_motive_1010_, v_t_boxed_1014_, v_h_1012_, v_preferSticky_1013_);
lean_dec(v_preferSticky_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(lean_object* v_preferUnsticky_1016_){
_start:
{
lean_inc(v_preferUnsticky_1016_);
return v_preferUnsticky_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg___boxed(lean_object* v_preferUnsticky_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(v_preferUnsticky_1017_);
lean_dec(v_preferUnsticky_1017_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(lean_object* v_motive_1019_, uint8_t v_t_1020_, lean_object* v_h_1021_, lean_object* v_preferUnsticky_1022_){
_start:
{
lean_inc(v_preferUnsticky_1022_);
return v_preferUnsticky_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___boxed(lean_object* v_motive_1023_, lean_object* v_t_1024_, lean_object* v_h_1025_, lean_object* v_preferUnsticky_1026_){
_start:
{
uint8_t v_t_boxed_1027_; lean_object* v_res_1028_; 
v_t_boxed_1027_ = lean_unbox(v_t_1024_);
v_res_1028_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(v_motive_1023_, v_t_boxed_1027_, v_h_1025_, v_preferUnsticky_1026_);
lean_dec(v_preferUnsticky_1026_);
return v_res_1028_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default(void){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = 0;
return v___x_1029_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind(void){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = 0;
return v___x_1030_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t v_x_1031_, uint8_t v_y_1032_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1033_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_x_1031_);
v___x_1034_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_y_1032_);
v___x_1035_ = lean_nat_dec_eq(v___x_1033_, v___x_1034_);
lean_dec(v___x_1034_);
lean_dec(v___x_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed(lean_object* v_x_1036_, lean_object* v_y_1037_){
_start:
{
uint8_t v_x_21__boxed_1038_; uint8_t v_y_22__boxed_1039_; uint8_t v_res_1040_; lean_object* v_r_1041_; 
v_x_21__boxed_1038_ = lean_unbox(v_x_1036_);
v_y_22__boxed_1039_ = lean_unbox(v_y_1037_);
v_res_1040_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_x_21__boxed_1038_, v_y_22__boxed_1039_);
v_r_1041_ = lean_box(v_res_1040_);
return v_r_1041_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0(void){
_start:
{
uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = 0;
v___x_1045_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1046_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*1, v___x_1044_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default(void){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0, &l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky(void){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___lam__0(lean_object* v_v_1060_, lean_object* v_f_1061_){
_start:
{
lean_object* v_stickyVariant_1062_; uint8_t v_kind_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_stickyVariant_1062_ = lean_ctor_get(v_v_1060_, 0);
v_kind_1063_ = lean_ctor_get_uint8(v_v_1060_, sizeof(void*)*1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_v_1060_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1065_ = v_v_1060_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_stickyVariant_1062_);
lean_dec(v_v_1060_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_stickyVariant_1062_, v_f_1061_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
lean_ctor_set_uint8(v_reuseFailAlloc_1070_, sizeof(void*)*1, v_kind_1063_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object* v_nonStickyVariant_1073_, lean_object* v_stickyVariant_1074_, uint8_t v_kind_1075_){
_start:
{
lean_object* v___f_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___f_1076_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_sticky___closed__0));
v___x_1077_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1078_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1079_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1079_, 0, v_stickyVariant_1074_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*1, v_kind_1075_);
v___x_1080_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1077_, v___x_1078_, v_nonStickyVariant_1073_, v___x_1079_, v___f_1076_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___boxed(lean_object* v_nonStickyVariant_1081_, lean_object* v_stickyVariant_1082_, lean_object* v_kind_1083_){
_start:
{
uint8_t v_kind_boxed_1084_; lean_object* v_res_1085_; 
v_kind_boxed_1084_ = lean_unbox(v_kind_1083_);
v_res_1085_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_1081_, v_stickyVariant_1082_, v_kind_boxed_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object* v_doc_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1088_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1087_, v_doc_1086_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object* v_doc_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_doc_1089_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
else
{
lean_object* v_val_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1101_; 
v_val_1092_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1094_ = v___x_1090_;
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_val_1092_);
lean_dec(v___x_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1101_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
uint8_t v_kind_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v_kind_1096_ = lean_ctor_get_uint8(v_val_1092_, sizeof(void*)*1);
lean_dec(v_val_1092_);
v___x_1097_ = lean_box(v_kind_1096_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object* v_inner_1102_, lean_object* v_f_1103_, lean_object* v_kind_x3f_1104_){
_start:
{
lean_object* v_nonStickyOuter_1105_; lean_object* v___x_1106_; 
lean_inc_ref(v_f_1103_);
lean_inc_ref(v_inner_1102_);
v_nonStickyOuter_1105_ = lean_apply_1(v_f_1103_, v_inner_1102_);
v___x_1106_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_inner_1102_);
if (lean_obj_tag(v___x_1106_) == 1)
{
lean_object* v_val_1107_; lean_object* v_stickyVariant_1108_; uint8_t v_kind_1109_; lean_object* v_stickyOuter_1110_; 
v_val_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_val_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v_stickyVariant_1108_ = lean_ctor_get(v_val_1107_, 0);
lean_inc_ref(v_stickyVariant_1108_);
v_kind_1109_ = lean_ctor_get_uint8(v_val_1107_, sizeof(void*)*1);
lean_dec(v_val_1107_);
v_stickyOuter_1110_ = lean_apply_1(v_f_1103_, v_stickyVariant_1108_);
if (lean_obj_tag(v_kind_x3f_1104_) == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1105_, v_stickyOuter_1110_, v_kind_1109_);
return v___x_1111_;
}
else
{
lean_object* v_val_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; 
v_val_1112_ = lean_ctor_get(v_kind_x3f_1104_, 0);
v___x_1113_ = lean_unbox(v_val_1112_);
v___x_1114_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1105_, v_stickyOuter_1110_, v___x_1113_);
return v___x_1114_;
}
}
else
{
lean_dec(v___x_1106_);
lean_dec_ref(v_f_1103_);
return v_nonStickyOuter_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness___boxed(lean_object* v_inner_1115_, lean_object* v_f_1116_, lean_object* v_kind_x3f_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_inner_1115_, v_f_1116_, v_kind_x3f_1117_);
lean_dec(v_kind_x3f_1117_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx(lean_object* v_x_1119_){
_start:
{
switch(lean_obj_tag(v_x_1119_))
{
case 0:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
return v___x_1120_;
}
case 1:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_unsigned_to_nat(1u);
return v___x_1121_;
}
default: 
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_unsigned_to_nat(2u);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___boxed(lean_object* v_x_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx(v_x_1123_);
lean_dec(v_x_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(lean_object* v_t_1125_, lean_object* v_k_1126_){
_start:
{
if (lean_obj_tag(v_t_1125_) == 2)
{
uint8_t v_allowFlattening_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_allowFlattening_1127_ = lean_ctor_get_uint8(v_t_1125_, 0);
v___x_1128_ = lean_box(v_allowFlattening_1127_);
v___x_1129_ = lean_apply_1(v_k_1126_, v___x_1128_);
return v___x_1129_;
}
else
{
return v_k_1126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg___boxed(lean_object* v_t_1130_, lean_object* v_k_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1130_, v_k_1131_);
lean_dec(v_t_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(lean_object* v_motive_1133_, lean_object* v_ctorIdx_1134_, lean_object* v_t_1135_, lean_object* v_h_1136_, lean_object* v_k_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1135_, v_k_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___boxed(lean_object* v_motive_1139_, lean_object* v_ctorIdx_1140_, lean_object* v_t_1141_, lean_object* v_h_1142_, lean_object* v_k_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(v_motive_1139_, v_ctorIdx_1140_, v_t_1141_, v_h_1142_, v_k_1143_);
lean_dec(v_t_1141_);
lean_dec(v_ctorIdx_1140_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(lean_object* v_t_1145_, lean_object* v_coequal_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1145_, v_coequal_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg___boxed(lean_object* v_t_1148_, lean_object* v_coequal_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(v_t_1148_, v_coequal_1149_);
lean_dec(v_t_1148_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(lean_object* v_motive_1151_, lean_object* v_t_1152_, lean_object* v_h_1153_, lean_object* v_coequal_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1152_, v_coequal_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___boxed(lean_object* v_motive_1156_, lean_object* v_t_1157_, lean_object* v_h_1158_, lean_object* v_coequal_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(v_motive_1156_, v_t_1157_, v_h_1158_, v_coequal_1159_);
lean_dec(v_t_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(lean_object* v_t_1161_, lean_object* v_preferUnsticky_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1161_, v_preferUnsticky_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg___boxed(lean_object* v_t_1164_, lean_object* v_preferUnsticky_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(v_t_1164_, v_preferUnsticky_1165_);
lean_dec(v_t_1164_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(lean_object* v_motive_1167_, lean_object* v_t_1168_, lean_object* v_h_1169_, lean_object* v_preferUnsticky_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1168_, v_preferUnsticky_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___boxed(lean_object* v_motive_1172_, lean_object* v_t_1173_, lean_object* v_h_1174_, lean_object* v_preferUnsticky_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(v_motive_1172_, v_t_1173_, v_h_1174_, v_preferUnsticky_1175_);
lean_dec(v_t_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(lean_object* v_t_1177_, lean_object* v_preferSticky_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1177_, v_preferSticky_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg___boxed(lean_object* v_t_1180_, lean_object* v_preferSticky_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(v_t_1180_, v_preferSticky_1181_);
lean_dec(v_t_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(lean_object* v_motive_1183_, lean_object* v_t_1184_, lean_object* v_h_1185_, lean_object* v_preferSticky_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1184_, v_preferSticky_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___boxed(lean_object* v_motive_1188_, lean_object* v_t_1189_, lean_object* v_h_1190_, lean_object* v_preferSticky_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(v_motive_1188_, v_t_1189_, v_h_1190_, v_preferSticky_1191_);
lean_dec(v_t_1189_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object* v_s_1193_, uint8_t v_allowFlattening_1194_){
_start:
{
uint8_t v_kind_1195_; 
v_kind_1195_ = lean_ctor_get_uint8(v_s_1193_, sizeof(void*)*1);
switch(v_kind_1195_)
{
case 0:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_box(0);
return v___x_1196_;
}
case 1:
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1197_, 0, v_allowFlattening_1194_);
return v___x_1197_;
}
default: 
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_box(1);
return v___x_1198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky___boxed(lean_object* v_s_1199_, lean_object* v_allowFlattening_1200_){
_start:
{
uint8_t v_allowFlattening_boxed_1201_; lean_object* v_res_1202_; 
v_allowFlattening_boxed_1201_ = lean_unbox(v_allowFlattening_1200_);
v_res_1202_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_s_1199_, v_allowFlattening_boxed_1201_);
lean_dec_ref(v_s_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object* v_doc_1203_, lean_object* v_stickyDoc_1204_, lean_object* v_cfg_1205_){
_start:
{
switch(lean_obj_tag(v_cfg_1205_))
{
case 0:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1206_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1204_);
v___x_1207_ = lean_unsigned_to_nat(2u);
v___x_1208_ = lean_mk_empty_array_with_capacity(v___x_1207_);
v___x_1209_ = lean_array_push(v___x_1208_, v___x_1206_);
v___x_1210_ = lean_array_push(v___x_1209_, v_doc_1203_);
v___x_1211_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1210_);
return v___x_1211_;
}
case 1:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1212_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1204_);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v___x_1212_, v___x_1213_);
v___x_1215_ = lean_unsigned_to_nat(2u);
v___x_1216_ = lean_mk_empty_array_with_capacity(v___x_1215_);
v___x_1217_ = lean_array_push(v___x_1216_, v_doc_1203_);
v___x_1218_ = lean_array_push(v___x_1217_, v___x_1214_);
v___x_1219_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1218_);
return v___x_1219_;
}
default: 
{
uint8_t v_allowFlattening_1220_; 
v_allowFlattening_1220_ = lean_ctor_get_uint8(v_cfg_1205_, 0);
if (v_allowFlattening_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1221_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1204_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1203_, v___x_1222_);
v___x_1224_ = lean_unsigned_to_nat(2u);
v___x_1225_ = lean_mk_empty_array_with_capacity(v___x_1224_);
v___x_1226_ = lean_array_push(v___x_1225_, v___x_1221_);
v___x_1227_ = lean_array_push(v___x_1226_, v___x_1223_);
v___x_1228_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1227_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1229_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1204_);
lean_inc_ref(v_doc_1203_);
v___x_1230_ = l_Lean_Fmt_TaggedDoc_flattened(v_doc_1203_);
v___x_1231_ = lean_unsigned_to_nat(1u);
v___x_1232_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1203_, v___x_1231_);
v___x_1233_ = lean_unsigned_to_nat(3u);
v___x_1234_ = lean_mk_empty_array_with_capacity(v___x_1233_);
v___x_1235_ = lean_array_push(v___x_1234_, v___x_1229_);
v___x_1236_ = lean_array_push(v___x_1235_, v___x_1230_);
v___x_1237_ = lean_array_push(v___x_1236_, v___x_1232_);
v___x_1238_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1237_);
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt___boxed(lean_object* v_doc_1239_, lean_object* v_stickyDoc_1240_, lean_object* v_cfg_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1239_, v_stickyDoc_1240_, v_cfg_1241_);
lean_dec(v_cfg_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0(lean_object* v_s_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0));
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_s_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0(lean_object* v_doc_x3f_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
lean_ctor_set(v___x_1251_, 1, v_doc_x3f_1249_);
lean_ctor_set(v___x_1251_, 2, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object* v_doc_x3f_1254_, lean_object* v_sepBefore_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_sepBefore_1255_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v_doc_x3f_1254_);
lean_ctor_set(v___x_1258_, 2, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object* v_doc_x3f_1259_, lean_object* v_sepAfter_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_sepAfter_1260_);
v___x_1263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1261_);
lean_ctor_set(v___x_1263_, 1, v_doc_x3f_1259_);
lean_ctor_set(v___x_1263_, 2, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(lean_object* v_as_1264_, size_t v_i_1265_, size_t v_stop_1266_, lean_object* v_b_1267_){
_start:
{
lean_object* v___y_1269_; uint8_t v___x_1273_; 
v___x_1273_ = lean_usize_dec_eq(v_i_1265_, v_stop_1266_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; lean_object* v_doc_x3f_1275_; 
v___x_1274_ = lean_array_uget_borrowed(v_as_1264_, v_i_1265_);
v_doc_x3f_1275_ = lean_ctor_get(v___x_1274_, 1);
if (lean_obj_tag(v_doc_x3f_1275_) == 0)
{
v___y_1269_ = v_b_1267_;
goto v___jp_1268_;
}
else
{
lean_object* v_sepBefore_x3f_1276_; lean_object* v_sepAfter_x3f_1277_; lean_object* v_val_1278_; uint8_t v___x_1279_; 
v_sepBefore_x3f_1276_ = lean_ctor_get(v___x_1274_, 0);
v_sepAfter_x3f_1277_ = lean_ctor_get(v___x_1274_, 2);
v_val_1278_ = lean_ctor_get(v_doc_x3f_1275_, 0);
v___x_1279_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_inc(v_sepAfter_x3f_1277_);
lean_inc(v_val_1278_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_val_1278_);
lean_ctor_set(v___x_1280_, 1, v_sepAfter_x3f_1277_);
lean_inc(v_sepBefore_x3f_1276_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v_sepBefore_x3f_1276_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = lean_array_push(v_b_1267_, v___x_1281_);
v___y_1269_ = v___x_1282_;
goto v___jp_1268_;
}
else
{
v___y_1269_ = v_b_1267_;
goto v___jp_1268_;
}
}
}
else
{
return v_b_1267_;
}
v___jp_1268_:
{
size_t v___x_1270_; size_t v___x_1271_; 
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_add(v_i_1265_, v___x_1270_);
v_i_1265_ = v___x_1271_;
v_b_1267_ = v___y_1269_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0___boxed(lean_object* v_as_1283_, lean_object* v_i_1284_, lean_object* v_stop_1285_, lean_object* v_b_1286_){
_start:
{
size_t v_i_boxed_1287_; size_t v_stop_boxed_1288_; lean_object* v_res_1289_; 
v_i_boxed_1287_ = lean_unbox_usize(v_i_1284_);
lean_dec(v_i_1284_);
v_stop_boxed_1288_ = lean_unbox_usize(v_stop_1285_);
lean_dec(v_stop_1285_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1283_, v_i_boxed_1287_, v_stop_boxed_1288_, v_b_1286_);
lean_dec_ref(v_as_1283_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(lean_object* v_as_1292_, lean_object* v_start_1293_, lean_object* v_stop_1294_){
_start:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0));
v___x_1296_ = lean_nat_dec_lt(v_start_1293_, v_stop_1294_);
if (v___x_1296_ == 0)
{
return v___x_1295_;
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = lean_array_get_size(v_as_1292_);
v___x_1298_ = lean_nat_dec_le(v_stop_1294_, v___x_1297_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_nat_dec_lt(v_start_1293_, v___x_1297_);
if (v___x_1299_ == 0)
{
return v___x_1295_;
}
else
{
size_t v___x_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = lean_usize_of_nat(v_start_1293_);
v___x_1301_ = lean_usize_of_nat(v___x_1297_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1292_, v___x_1300_, v___x_1301_, v___x_1295_);
return v___x_1302_;
}
}
else
{
size_t v___x_1303_; size_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_usize_of_nat(v_start_1293_);
v___x_1304_ = lean_usize_of_nat(v_stop_1294_);
v___x_1305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1292_, v___x_1303_, v___x_1304_, v___x_1295_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___boxed(lean_object* v_as_1306_, lean_object* v_start_1307_, lean_object* v_stop_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_as_1306_, v_start_1307_, v_stop_1308_);
lean_dec(v_stop_1308_);
lean_dec(v_start_1307_);
lean_dec_ref(v_as_1306_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(lean_object* v_cs_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_array_get_size(v_cs_1310_);
v___x_1313_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_cs_1310_, v___x_1311_, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs___boxed(lean_object* v_cs_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1314_);
lean_dec_ref(v_cs_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_bs_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1319_ == 0)
{
return v_bs_1318_;
}
else
{
lean_object* v_v_1320_; lean_object* v_snd_1321_; lean_object* v_fst_1322_; lean_object* v_fst_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1336_; 
v_v_1320_ = lean_array_uget_borrowed(v_bs_1318_, v_i_1317_);
v_snd_1321_ = lean_ctor_get(v_v_1320_, 1);
lean_inc(v_snd_1321_);
v_fst_1322_ = lean_ctor_get(v_v_1320_, 0);
lean_inc(v_fst_1322_);
v_fst_1323_ = lean_ctor_get(v_snd_1321_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_snd_1321_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_snd_1321_, 1);
lean_dec(v_unused_1337_);
v___x_1325_ = v_snd_1321_;
v_isShared_1326_ = v_isSharedCheck_1336_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_fst_1323_);
lean_dec(v_snd_1321_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1336_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v_bs_x27_1328_; lean_object* v___x_1330_; 
v___x_1327_ = lean_unsigned_to_nat(0u);
v_bs_x27_1328_ = lean_array_uset(v_bs_1318_, v_i_1317_, v___x_1327_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 1, v_fst_1323_);
lean_ctor_set(v___x_1325_, 0, v_fst_1322_);
v___x_1330_ = v___x_1325_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_fst_1322_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_fst_1323_);
v___x_1330_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
size_t v___x_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = ((size_t)1ULL);
v___x_1332_ = lean_usize_add(v_i_1317_, v___x_1331_);
v___x_1333_ = lean_array_uset(v_bs_x27_1328_, v_i_1317_, v___x_1330_);
v_i_1317_ = v___x_1332_;
v_bs_1318_ = v___x_1333_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0___boxed(lean_object* v_sz_1338_, lean_object* v_i_1339_, lean_object* v_bs_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1338_);
lean_dec(v_sz_1338_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1339_);
lean_dec(v_i_1339_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_boxed_1341_, v_i_boxed_1342_, v_bs_1340_);
return v_res_1343_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___x_1344_);
return v___x_1346_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v___x_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(lean_object* v_upperBound_1350_, lean_object* v_a_1351_, lean_object* v_b_1352_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_lt(v_a_1351_, v_upperBound_1350_);
if (v___x_1353_ == 0)
{
lean_dec(v_a_1351_);
return v_b_1352_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v_snd_1356_; lean_object* v_snd_1357_; lean_object* v___x_1358_; lean_object* v_a_1360_; 
v___x_1354_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1355_ = lean_array_get_borrowed(v___x_1354_, v_b_1352_, v_a_1351_);
v_snd_1356_ = lean_ctor_get(v___x_1355_, 1);
v_snd_1357_ = lean_ctor_get(v_snd_1356_, 1);
v___x_1358_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1357_) == 1)
{
lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1363_ = lean_nat_add(v_a_1351_, v___x_1358_);
v___x_1364_ = lean_array_get_size(v_b_1352_);
v___x_1365_ = lean_nat_dec_lt(v___x_1363_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_dec(v___x_1363_);
v_a_1360_ = v_b_1352_;
goto v___jp_1359_;
}
else
{
lean_object* v_v_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1377_; 
lean_inc_ref(v_snd_1357_);
v_v_1366_ = lean_array_fget(v_b_1352_, v___x_1363_);
v_snd_1367_ = lean_ctor_get(v_v_1366_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_v_1366_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v_v_1366_, 0);
lean_dec(v_unused_1378_);
v___x_1369_ = v_v_1366_;
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_dec(v_v_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1377_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v_xs_x27_1372_; lean_object* v___x_1374_; 
v___x_1371_ = lean_box(0);
v_xs_x27_1372_ = lean_array_fset(v_b_1352_, v___x_1363_, v___x_1371_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v_snd_1357_);
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_snd_1357_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_snd_1367_);
v___x_1374_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_array_fset(v_xs_x27_1372_, v___x_1363_, v___x_1374_);
lean_dec(v___x_1363_);
v_a_1360_ = v___x_1375_;
goto v___jp_1359_;
}
}
}
}
else
{
v_a_1360_ = v_b_1352_;
goto v___jp_1359_;
}
v___jp_1359_:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_nat_add(v_a_1351_, v___x_1358_);
lean_dec(v_a_1351_);
v_a_1351_ = v___x_1361_;
v_b_1352_ = v_a_1360_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___boxed(lean_object* v_upperBound_1379_, lean_object* v_a_1380_, lean_object* v_b_1381_){
_start:
{
lean_object* v_res_1382_; 
v_res_1382_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1379_, v_a_1380_, v_b_1381_);
lean_dec(v_upperBound_1379_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(lean_object* v_upperBound_1383_, lean_object* v_a_1384_, lean_object* v_b_1385_){
_start:
{
uint8_t v___x_1386_; 
v___x_1386_ = lean_nat_dec_lt(v_a_1384_, v_upperBound_1383_);
if (v___x_1386_ == 0)
{
lean_dec(v_a_1384_);
return v_b_1385_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_snd_1390_; lean_object* v_snd_1391_; lean_object* v___x_1392_; lean_object* v_a_1394_; 
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1389_ = lean_array_get_borrowed(v___x_1388_, v_b_1385_, v_a_1384_);
v_snd_1390_ = lean_ctor_get(v___x_1389_, 1);
v_snd_1391_ = lean_ctor_get(v_snd_1390_, 1);
v___x_1392_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1391_) == 1)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_fst_1399_; 
v___x_1397_ = lean_nat_add(v_a_1384_, v___x_1392_);
v___x_1398_ = lean_array_get_borrowed(v___x_1388_, v_b_1385_, v___x_1397_);
lean_dec(v___x_1397_);
v_fst_1399_ = lean_ctor_get(v___x_1398_, 0);
if (lean_obj_tag(v_fst_1399_) == 1)
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = lean_array_get_size(v_b_1385_);
v___x_1401_ = lean_nat_dec_lt(v_a_1384_, v___x_1400_);
if (v___x_1401_ == 0)
{
v_a_1394_ = v_b_1385_;
goto v___jp_1393_;
}
else
{
lean_object* v_v_1402_; lean_object* v_snd_1403_; lean_object* v_fst_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1423_; 
v_v_1402_ = lean_array_fget(v_b_1385_, v_a_1384_);
v_snd_1403_ = lean_ctor_get(v_v_1402_, 1);
v_fst_1404_ = lean_ctor_get(v_v_1402_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_v_1402_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1406_ = v_v_1402_;
v_isShared_1407_ = v_isSharedCheck_1423_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_snd_1403_);
lean_inc(v_fst_1404_);
lean_dec(v_v_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1423_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_fst_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1421_; 
v_fst_1408_ = lean_ctor_get(v_snd_1403_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_snd_1403_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_snd_1403_, 1);
lean_dec(v_unused_1422_);
v___x_1410_ = v_snd_1403_;
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_fst_1408_);
lean_dec(v_snd_1403_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1421_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v_xs_x27_1413_; lean_object* v___x_1415_; 
v___x_1412_ = lean_box(0);
v_xs_x27_1413_ = lean_array_fset(v_b_1385_, v_a_1384_, v___x_1412_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___x_1387_);
v___x_1415_ = v___x_1410_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_fst_1408_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v___x_1387_);
v___x_1415_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 1, v___x_1415_);
v___x_1417_ = v___x_1406_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_fst_1404_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_array_fset(v_xs_x27_1413_, v_a_1384_, v___x_1417_);
v_a_1394_ = v___x_1418_;
goto v___jp_1393_;
}
}
}
}
}
}
else
{
v_a_1394_ = v_b_1385_;
goto v___jp_1393_;
}
}
else
{
v_a_1394_ = v_b_1385_;
goto v___jp_1393_;
}
v___jp_1393_:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_nat_add(v_a_1384_, v___x_1392_);
lean_dec(v_a_1384_);
v_a_1384_ = v___x_1395_;
v_b_1385_ = v_a_1394_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg___boxed(lean_object* v_upperBound_1424_, lean_object* v_a_1425_, lean_object* v_b_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1424_, v_a_1425_, v_b_1426_);
lean_dec(v_upperBound_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(lean_object* v_upperBound_1428_, lean_object* v_a_1429_, lean_object* v_b_1430_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = lean_nat_dec_lt(v_a_1429_, v_upperBound_1428_);
if (v___x_1431_ == 0)
{
return v_b_1430_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v_snd_1435_; lean_object* v_snd_1436_; lean_object* v___x_1437_; lean_object* v_a_1439_; 
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1434_ = lean_array_get_borrowed(v___x_1433_, v_b_1430_, v_a_1429_);
v_snd_1435_ = lean_ctor_get(v___x_1434_, 1);
v_snd_1436_ = lean_ctor_get(v_snd_1435_, 1);
v___x_1437_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1436_) == 1)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_fst_1444_; 
v___x_1442_ = lean_nat_add(v_a_1429_, v___x_1437_);
v___x_1443_ = lean_array_get_borrowed(v___x_1433_, v_b_1430_, v___x_1442_);
lean_dec(v___x_1442_);
v_fst_1444_ = lean_ctor_get(v___x_1443_, 0);
if (lean_obj_tag(v_fst_1444_) == 1)
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = lean_array_get_size(v_b_1430_);
v___x_1446_ = lean_nat_dec_lt(v_a_1429_, v___x_1445_);
if (v___x_1446_ == 0)
{
v_a_1439_ = v_b_1430_;
goto v___jp_1438_;
}
else
{
lean_object* v_v_1447_; lean_object* v_snd_1448_; lean_object* v_fst_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1468_; 
v_v_1447_ = lean_array_fget(v_b_1430_, v_a_1429_);
v_snd_1448_ = lean_ctor_get(v_v_1447_, 1);
v_fst_1449_ = lean_ctor_get(v_v_1447_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_v_1447_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1451_ = v_v_1447_;
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snd_1448_);
lean_inc(v_fst_1449_);
lean_dec(v_v_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_fst_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1466_; 
v_fst_1453_ = lean_ctor_get(v_snd_1448_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_snd_1448_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_snd_1448_, 1);
lean_dec(v_unused_1467_);
v___x_1455_ = v_snd_1448_;
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_fst_1453_);
lean_dec(v_snd_1448_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v_xs_x27_1458_; lean_object* v___x_1460_; 
v___x_1457_ = lean_box(0);
v_xs_x27_1458_ = lean_array_fset(v_b_1430_, v_a_1429_, v___x_1457_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v___x_1432_);
v___x_1460_ = v___x_1455_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_fst_1453_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1432_);
v___x_1460_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1460_);
v___x_1462_ = v___x_1451_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_fst_1449_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_array_fset(v_xs_x27_1458_, v_a_1429_, v___x_1462_);
v_a_1439_ = v___x_1463_;
goto v___jp_1438_;
}
}
}
}
}
}
else
{
v_a_1439_ = v_b_1430_;
goto v___jp_1438_;
}
}
else
{
v_a_1439_ = v_b_1430_;
goto v___jp_1438_;
}
v___jp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_nat_add(v_a_1429_, v___x_1437_);
v___x_1441_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1428_, v___x_1440_, v_a_1439_);
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg___boxed(lean_object* v_upperBound_1469_, lean_object* v_a_1470_, lean_object* v_b_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1469_, v_a_1470_, v_b_1471_);
lean_dec(v_a_1470_);
lean_dec(v_upperBound_1469_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(lean_object* v_entries_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1488_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1516_ = lean_array_get_size(v_entries_1473_);
v___x_1517_ = lean_nat_dec_lt(v___x_1474_, v___x_1516_);
if (v___x_1517_ == 0)
{
v___y_1488_ = v_entries_1473_;
goto v___jp_1487_;
}
else
{
lean_object* v_v_1518_; lean_object* v_snd_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1530_; 
v_v_1518_ = lean_array_fget(v_entries_1473_, v___x_1474_);
v_snd_1519_ = lean_ctor_get(v_v_1518_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_v_1518_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_v_1518_, 0);
lean_dec(v_unused_1531_);
v___x_1521_ = v_v_1518_;
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_snd_1519_);
lean_dec(v_v_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1530_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v_xs_x27_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1523_ = lean_box(0);
v_xs_x27_1524_ = lean_array_fset(v_entries_1473_, v___x_1474_, v___x_1523_);
v___x_1525_ = lean_box(0);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1525_);
v___x_1527_ = v___x_1521_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_snd_1519_);
v___x_1527_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_array_fset(v_xs_x27_1524_, v___x_1474_, v___x_1527_);
v___y_1488_ = v___x_1528_;
goto v___jp_1487_;
}
}
}
v___jp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; size_t v_sz_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1478_ = lean_array_get_size(v___y_1477_);
v___x_1479_ = lean_nat_sub(v___x_1478_, v___y_1476_);
v___x_1480_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v___x_1479_, v___x_1474_, v___y_1477_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_array_get_size(v___x_1480_);
v___x_1482_ = lean_nat_sub(v___x_1481_, v___y_1476_);
v___x_1483_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v___x_1482_, v___x_1474_, v___x_1480_);
lean_dec(v___x_1482_);
v_sz_1484_ = lean_array_size(v___x_1483_);
v___x_1485_ = ((size_t)0ULL);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_1484_, v___x_1485_, v___x_1483_);
return v___x_1486_;
}
v___jp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; uint8_t v___x_1492_; 
v___x_1489_ = lean_array_get_size(v___y_1488_);
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_sub(v___x_1489_, v___x_1490_);
v___x_1492_ = lean_nat_dec_lt(v___x_1491_, v___x_1489_);
if (v___x_1492_ == 0)
{
lean_dec(v___x_1491_);
v___y_1476_ = v___x_1490_;
v___y_1477_ = v___y_1488_;
goto v___jp_1475_;
}
else
{
lean_object* v_v_1493_; lean_object* v_snd_1494_; lean_object* v_fst_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1515_; 
v_v_1493_ = lean_array_fget(v___y_1488_, v___x_1491_);
v_snd_1494_ = lean_ctor_get(v_v_1493_, 1);
v_fst_1495_ = lean_ctor_get(v_v_1493_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_v_1493_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1497_ = v_v_1493_;
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_snd_1494_);
lean_inc(v_fst_1495_);
lean_dec(v_v_1493_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_fst_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1513_; 
v_fst_1499_ = lean_ctor_get(v_snd_1494_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_snd_1494_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_snd_1494_, 1);
lean_dec(v_unused_1514_);
v___x_1501_ = v_snd_1494_;
v_isShared_1502_ = v_isSharedCheck_1513_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_fst_1499_);
lean_dec(v_snd_1494_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1513_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v_xs_x27_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1503_ = lean_box(0);
v_xs_x27_1504_ = lean_array_fset(v___y_1488_, v___x_1491_, v___x_1503_);
v___x_1505_ = lean_box(0);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 1, v___x_1505_);
v___x_1507_ = v___x_1501_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_fst_1499_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v___x_1507_);
v___x_1509_ = v___x_1497_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_fst_1495_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_array_fset(v_xs_x27_1504_, v___x_1491_, v___x_1509_);
lean_dec(v___x_1491_);
v___y_1476_ = v___x_1490_;
v___y_1477_ = v___x_1510_;
goto v___jp_1475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(lean_object* v_upperBound_1532_, lean_object* v_inst_1533_, lean_object* v_R_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v_c_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1532_, v_a_1535_, v_b_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___boxed(lean_object* v_upperBound_1539_, lean_object* v_inst_1540_, lean_object* v_R_1541_, lean_object* v_a_1542_, lean_object* v_b_1543_, lean_object* v_c_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(v_upperBound_1539_, v_inst_1540_, v_R_1541_, v_a_1542_, v_b_1543_, v_c_1544_);
lean_dec(v_upperBound_1539_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(lean_object* v_upperBound_1546_, lean_object* v_inst_1547_, lean_object* v_R_1548_, lean_object* v_a_1549_, lean_object* v_b_1550_, lean_object* v_c_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1546_, v_a_1549_, v_b_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___boxed(lean_object* v_upperBound_1553_, lean_object* v_inst_1554_, lean_object* v_R_1555_, lean_object* v_a_1556_, lean_object* v_b_1557_, lean_object* v_c_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(v_upperBound_1553_, v_inst_1554_, v_R_1555_, v_a_1556_, v_b_1557_, v_c_1558_);
lean_dec(v_a_1556_);
lean_dec(v_upperBound_1553_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(lean_object* v_upperBound_1560_, lean_object* v_inst_1561_, lean_object* v_R_1562_, lean_object* v_a_1563_, lean_object* v_b_1564_, lean_object* v_c_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1560_, v_a_1563_, v_b_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___boxed(lean_object* v_upperBound_1567_, lean_object* v_inst_1568_, lean_object* v_R_1569_, lean_object* v_a_1570_, lean_object* v_b_1571_, lean_object* v_c_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(v_upperBound_1567_, v_inst_1568_, v_R_1569_, v_a_1570_, v_b_1571_, v_c_1572_);
lean_dec(v_upperBound_1567_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(lean_object* v_as_1574_, size_t v_sz_1575_, size_t v_i_1576_, lean_object* v_b_1577_){
_start:
{
lean_object* v_a_1579_; uint8_t v___x_1583_; 
v___x_1583_ = lean_usize_dec_lt(v_i_1576_, v_sz_1575_);
if (v___x_1583_ == 0)
{
return v_b_1577_;
}
else
{
lean_object* v_a_1584_; lean_object* v_fst_1585_; 
v_a_1584_ = lean_array_uget_borrowed(v_as_1574_, v_i_1576_);
v_fst_1585_ = lean_ctor_get(v_a_1584_, 0);
if (lean_obj_tag(v_fst_1585_) == 1)
{
lean_object* v_val_1586_; lean_object* v_snd_1587_; lean_object* v_s_1588_; lean_object* v_wrap_1589_; lean_object* v___y_1591_; lean_object* v___y_1594_; uint8_t v___x_1605_; 
v_val_1586_ = lean_ctor_get(v_fst_1585_, 0);
v_snd_1587_ = lean_ctor_get(v_a_1584_, 1);
v_s_1588_ = lean_ctor_get(v_val_1586_, 0);
v_wrap_1589_ = lean_ctor_get(v_val_1586_, 1);
v___x_1605_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_s_1588_);
if (v___x_1605_ == 0)
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1587_);
if (v___x_1606_ == 0)
{
lean_object* v_doc_1607_; lean_object* v_doc_1608_; uint8_t v___x_1609_; 
v_doc_1607_ = lean_ctor_get(v_s_1588_, 0);
v_doc_1608_ = lean_ctor_get(v_snd_1587_, 0);
v___x_1609_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1607_);
if (v___x_1609_ == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1608_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_inc(v_doc_1608_);
lean_inc(v_doc_1607_);
v___x_1611_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1607_, v_doc_1608_);
v___x_1612_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1611_);
v___y_1594_ = v___x_1612_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1613_; 
lean_inc(v_doc_1607_);
v___x_1613_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1607_);
v___y_1594_ = v___x_1613_;
goto v___jp_1593_;
}
}
else
{
lean_object* v___x_1614_; 
lean_inc(v_doc_1608_);
v___x_1614_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1608_);
v___y_1594_ = v___x_1614_;
goto v___jp_1593_;
}
}
else
{
lean_inc_ref(v_s_1588_);
v___y_1594_ = v_s_1588_;
goto v___jp_1593_;
}
}
else
{
lean_inc(v_snd_1587_);
v___y_1594_ = v_snd_1587_;
goto v___jp_1593_;
}
v___jp_1590_:
{
lean_object* v___x_1592_; 
lean_inc_ref(v_wrap_1589_);
v___x_1592_ = lean_apply_1(v_wrap_1589_, v___y_1591_);
v_a_1579_ = v___x_1592_;
goto v___jp_1578_;
}
v___jp_1593_:
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1594_);
if (v___x_1595_ == 0)
{
uint8_t v___x_1596_; 
v___x_1596_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1577_);
if (v___x_1596_ == 0)
{
lean_object* v_doc_1597_; lean_object* v_doc_1598_; uint8_t v___x_1599_; 
v_doc_1597_ = lean_ctor_get(v___y_1594_, 0);
lean_inc(v_doc_1597_);
lean_dec_ref(v___y_1594_);
v_doc_1598_ = lean_ctor_get(v_b_1577_, 0);
lean_inc(v_doc_1598_);
lean_dec_ref(v_b_1577_);
v___x_1599_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1597_);
if (v___x_1599_ == 0)
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1598_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1597_, v_doc_1598_);
v___x_1602_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1601_);
v___y_1591_ = v___x_1602_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1603_; 
lean_dec(v_doc_1598_);
v___x_1603_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1597_);
v___y_1591_ = v___x_1603_;
goto v___jp_1590_;
}
}
else
{
lean_object* v___x_1604_; 
lean_dec(v_doc_1597_);
v___x_1604_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1598_);
v___y_1591_ = v___x_1604_;
goto v___jp_1590_;
}
}
else
{
lean_dec_ref(v_b_1577_);
v___y_1591_ = v___y_1594_;
goto v___jp_1590_;
}
}
else
{
lean_dec_ref(v___y_1594_);
v___y_1591_ = v_b_1577_;
goto v___jp_1590_;
}
}
}
else
{
lean_object* v_snd_1615_; uint8_t v___x_1616_; 
v_snd_1615_ = lean_ctor_get(v_a_1584_, 1);
v___x_1616_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1615_);
if (v___x_1616_ == 0)
{
uint8_t v___x_1617_; 
v___x_1617_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1577_);
if (v___x_1617_ == 0)
{
lean_object* v_doc_1618_; lean_object* v_doc_1619_; uint8_t v___x_1620_; 
v_doc_1618_ = lean_ctor_get(v_snd_1615_, 0);
v_doc_1619_ = lean_ctor_get(v_b_1577_, 0);
lean_inc(v_doc_1619_);
lean_dec_ref(v_b_1577_);
v___x_1620_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1618_);
if (v___x_1620_ == 0)
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1619_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_inc(v_doc_1618_);
v___x_1622_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1618_, v_doc_1619_);
v___x_1623_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1622_);
v_a_1579_ = v___x_1623_;
goto v___jp_1578_;
}
else
{
lean_object* v___x_1624_; 
lean_dec(v_doc_1619_);
lean_inc(v_doc_1618_);
v___x_1624_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1618_);
v_a_1579_ = v___x_1624_;
goto v___jp_1578_;
}
}
else
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1619_);
v_a_1579_ = v___x_1625_;
goto v___jp_1578_;
}
}
else
{
lean_dec_ref(v_b_1577_);
lean_inc(v_snd_1615_);
v_a_1579_ = v_snd_1615_;
goto v___jp_1578_;
}
}
else
{
v_a_1579_ = v_b_1577_;
goto v___jp_1578_;
}
}
}
v___jp_1578_:
{
size_t v___x_1580_; size_t v___x_1581_; 
v___x_1580_ = ((size_t)1ULL);
v___x_1581_ = lean_usize_add(v_i_1576_, v___x_1580_);
v_i_1576_ = v___x_1581_;
v_b_1577_ = v_a_1579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0___boxed(lean_object* v_as_1626_, lean_object* v_sz_1627_, lean_object* v_i_1628_, lean_object* v_b_1629_){
_start:
{
size_t v_sz_boxed_1630_; size_t v_i_boxed_1631_; lean_object* v_res_1632_; 
v_sz_boxed_1630_ = lean_unbox_usize(v_sz_1627_);
lean_dec(v_sz_1627_);
v_i_boxed_1631_ = lean_unbox_usize(v_i_1628_);
lean_dec(v_i_1628_);
v_res_1632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v_as_1626_, v_sz_boxed_1630_, v_i_boxed_1631_, v_b_1629_);
lean_dec_ref(v_as_1626_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object* v_cs_1633_){
_start:
{
lean_object* v_entries_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v_entries_1634_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1633_);
v___x_1635_ = lean_array_get_size(v_entries_1634_);
v___x_1636_ = lean_unsigned_to_nat(0u);
v___x_1637_ = lean_nat_dec_eq(v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = lean_unsigned_to_nat(1u);
v___x_1639_ = lean_nat_dec_eq(v___x_1635_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v_entries_1640_; lean_object* v_combined_1641_; lean_object* v___x_1642_; size_t v_sz_1643_; size_t v___x_1644_; lean_object* v___x_1645_; 
v_entries_1640_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(v_entries_1634_);
v_combined_1641_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1642_ = l_Array_reverse___redArg(v_entries_1640_);
v_sz_1643_ = lean_array_size(v___x_1642_);
v___x_1644_ = ((size_t)0ULL);
v___x_1645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v___x_1642_, v_sz_1643_, v___x_1644_, v_combined_1641_);
lean_dec_ref(v___x_1642_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; lean_object* v_snd_1647_; lean_object* v_fst_1648_; 
v___x_1646_ = lean_array_fget(v_entries_1634_, v___x_1636_);
lean_dec_ref(v_entries_1634_);
v_snd_1647_ = lean_ctor_get(v___x_1646_, 1);
lean_inc(v_snd_1647_);
lean_dec(v___x_1646_);
v_fst_1648_ = lean_ctor_get(v_snd_1647_, 0);
lean_inc(v_fst_1648_);
lean_dec(v_snd_1647_);
return v_fst_1648_;
}
}
else
{
lean_object* v___x_1649_; 
lean_dec_ref(v_entries_1634_);
v___x_1649_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine___boxed(lean_object* v_cs_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_Fmt_TaggedDoc_combine(v_cs_1650_);
lean_dec_ref(v_cs_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object* v_lhs_1652_, lean_object* v_sep_1653_, lean_object* v_rhs_1654_, uint8_t v_allowFlattening_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v_nonStickyDoc_1665_; lean_object* v___x_1666_; 
v___x_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1656_, 0, v_lhs_1652_);
lean_inc_ref(v_sep_1653_);
lean_inc_ref(v___x_1656_);
v___x_1657_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1656_, v_sep_1653_);
v___x_1658_ = lean_box(0);
lean_inc_ref(v_rhs_1654_);
v___x_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_rhs_1654_);
v___x_1660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
lean_ctor_set(v___x_1660_, 2, v___x_1658_);
v___x_1661_ = lean_unsigned_to_nat(2u);
v___x_1662_ = lean_mk_empty_array_with_capacity(v___x_1661_);
lean_inc_ref(v___x_1662_);
v___x_1663_ = lean_array_push(v___x_1662_, v___x_1657_);
v___x_1664_ = lean_array_push(v___x_1663_, v___x_1660_);
v_nonStickyDoc_1665_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1664_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_1654_);
if (lean_obj_tag(v___x_1666_) == 1)
{
lean_object* v_val_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1692_; 
v_val_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1692_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_val_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1692_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v_wrap_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1690_; 
v_wrap_1671_ = lean_ctor_get(v_sep_1653_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_sep_1653_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v_sep_1653_, 0);
lean_dec(v_unused_1691_);
v___x_1673_ = v_sep_1653_;
v_isShared_1674_ = v_isSharedCheck_1690_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_wrap_1671_);
lean_dec(v_sep_1653_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1690_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_stickyVariant_1675_; lean_object* v___x_1676_; lean_object* v_stickySep_1678_; 
v_stickyVariant_1675_ = lean_ctor_get(v_val_1667_, 0);
v___x_1676_ = l_Lean_Fmt_TaggedDoc_space;
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1676_);
v_stickySep_1678_ = v___x_1673_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_wrap_1671_);
v_stickySep_1678_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1656_, v_stickySep_1678_);
lean_inc_ref(v_stickyVariant_1675_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 0, v_stickyVariant_1675_);
v___x_1681_ = v___x_1669_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_stickyVariant_1675_);
v___x_1681_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v_stickyDoc_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1658_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
lean_ctor_set(v___x_1682_, 2, v___x_1658_);
v___x_1683_ = lean_array_push(v___x_1662_, v___x_1679_);
v___x_1684_ = lean_array_push(v___x_1683_, v___x_1682_);
v_stickyDoc_1685_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1684_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_1667_, v_allowFlattening_1655_);
lean_dec(v_val_1667_);
v___x_1687_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_1665_, v_stickyDoc_1685_, v___x_1686_);
lean_dec(v___x_1686_);
return v___x_1687_;
}
}
}
}
}
else
{
lean_dec(v___x_1666_);
lean_dec_ref(v___x_1662_);
lean_dec_ref_known(v___x_1656_, 1);
lean_dec_ref(v_sep_1653_);
return v_nonStickyDoc_1665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine___boxed(lean_object* v_lhs_1693_, lean_object* v_sep_1694_, lean_object* v_rhs_1695_, lean_object* v_allowFlattening_1696_){
_start:
{
uint8_t v_allowFlattening_boxed_1697_; lean_object* v_res_1698_; 
v_allowFlattening_boxed_1697_ = lean_unbox(v_allowFlattening_1696_);
v_res_1698_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_1693_, v_sep_1694_, v_rhs_1695_, v_allowFlattening_boxed_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object* v_body_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(lean_object* v_f_1701_, size_t v_sz_1702_, size_t v_i_1703_, lean_object* v_bs_1704_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1703_, v_sz_1702_);
if (v___x_1705_ == 0)
{
lean_dec_ref(v_f_1701_);
return v_bs_1704_;
}
else
{
lean_object* v_v_1706_; lean_object* v___x_1707_; lean_object* v_bs_x27_1708_; lean_object* v___y_1710_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_v_1706_ = lean_array_uget(v_bs_1704_, v_i_1703_);
v___x_1707_ = lean_unsigned_to_nat(0u);
v_bs_x27_1708_ = lean_array_uset(v_bs_1704_, v_i_1703_, v___x_1707_);
v___x_1715_ = lean_usize_to_nat(v_i_1703_);
v___x_1716_ = lean_unsigned_to_nat(2u);
v___x_1717_ = lean_nat_mod(v___x_1715_, v___x_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_nat_dec_eq(v___x_1717_, v___x_1707_);
lean_dec(v___x_1717_);
if (v___x_1718_ == 0)
{
v___y_1710_ = v_v_1706_;
goto v___jp_1709_;
}
else
{
lean_object* v___x_1719_; 
lean_inc_ref(v_f_1701_);
v___x_1719_ = lean_apply_1(v_f_1701_, v_v_1706_);
v___y_1710_ = v___x_1719_;
goto v___jp_1709_;
}
v___jp_1709_:
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1703_, v___x_1711_);
v___x_1713_ = lean_array_uset(v_bs_x27_1708_, v_i_1703_, v___y_1710_);
v_i_1703_ = v___x_1712_;
v_bs_1704_ = v___x_1713_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg___boxed(lean_object* v_f_1720_, lean_object* v_sz_1721_, lean_object* v_i_1722_, lean_object* v_bs_1723_){
_start:
{
size_t v_sz_boxed_1724_; size_t v_i_boxed_1725_; lean_object* v_res_1726_; 
v_sz_boxed_1724_ = lean_unbox_usize(v_sz_1721_);
lean_dec(v_sz_1721_);
v_i_boxed_1725_ = lean_unbox_usize(v_i_1722_);
lean_dec(v_i_1722_);
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1720_, v_sz_boxed_1724_, v_i_boxed_1725_, v_bs_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(lean_object* v_a_1727_, lean_object* v_f_1728_){
_start:
{
size_t v_sz_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v_sz_1729_ = lean_array_size(v_a_1727_);
v___x_1730_ = ((size_t)0ULL);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1728_, v_sz_1729_, v___x_1730_, v_a_1727_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems(lean_object* v_sep_1732_, lean_object* v_a_1733_, lean_object* v_f_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(v_a_1733_, v_f_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___boxed(lean_object* v_sep_1736_, lean_object* v_a_1737_, lean_object* v_f_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems(v_sep_1736_, v_a_1737_, v_f_1738_);
lean_dec_ref(v_sep_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(lean_object* v_f_1740_, lean_object* v_as_1741_, size_t v_sz_1742_, size_t v_i_1743_, lean_object* v_bs_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1740_, v_sz_1742_, v_i_1743_, v_bs_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___boxed(lean_object* v_f_1746_, lean_object* v_as_1747_, lean_object* v_sz_1748_, lean_object* v_i_1749_, lean_object* v_bs_1750_){
_start:
{
size_t v_sz_boxed_1751_; size_t v_i_boxed_1752_; lean_object* v_res_1753_; 
v_sz_boxed_1751_ = lean_unbox_usize(v_sz_1748_);
lean_dec(v_sz_1748_);
v_i_boxed_1752_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(v_f_1746_, v_as_1747_, v_sz_boxed_1751_, v_i_boxed_1752_, v_bs_1750_);
lean_dec_ref(v_as_1747_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_pushElem(lean_object* v_sep_1754_, lean_object* v_a_1755_, lean_object* v_elem_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; uint8_t v___x_1761_; 
v___x_1757_ = lean_array_get_size(v_a_1755_);
v___x_1758_ = lean_unsigned_to_nat(2u);
v___x_1759_ = lean_nat_mod(v___x_1757_, v___x_1758_);
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_nat_dec_eq(v___x_1759_, v___x_1760_);
lean_dec(v___x_1759_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1762_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_1754_);
v___x_1763_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1762_);
v___x_1764_ = lean_mk_empty_array_with_capacity(v___x_1758_);
v___x_1765_ = lean_array_push(v___x_1764_, v___x_1763_);
v___x_1766_ = lean_array_push(v___x_1765_, v_elem_1756_);
v___x_1767_ = l_Array_append___redArg(v_a_1755_, v___x_1766_);
lean_dec_ref(v___x_1766_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; 
lean_dec_ref(v_sep_1754_);
v___x_1768_ = lean_array_push(v_a_1755_, v_elem_1756_);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_array_get_size(v_a_1769_);
v___x_1771_ = lean_unsigned_to_nat(1u);
v___x_1772_ = lean_nat_shiftr(v___x_1770_, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg___boxed(lean_object* v_a_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1773_);
lean_dec_ref(v_a_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems(lean_object* v_sep_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___boxed(lean_object* v_sep_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems(v_sep_1778_, v_a_1779_);
lean_dec_ref(v_a_1779_);
lean_dec_ref(v_sep_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(lean_object* v_docs_1781_){
_start:
{
lean_inc_ref(v_docs_1781_);
return v_docs_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0___boxed(lean_object* v_docs_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___lam__0(v_docs_1782_);
lean_dec_ref(v_docs_1782_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg(){
_start:
{
lean_object* v___f_1786_; 
v___f_1786_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___boxed(lean_object* v___dummy_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg();
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object* v_sep_1789_){
_start:
{
lean_object* v___f_1790_; 
v___f_1790_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object* v_sep_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(v_sep_1791_);
lean_dec_ref(v_sep_1791_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg(){
_start:
{
lean_object* v___f_1794_; 
v___f_1794_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg___boxed(lean_object* v___dummy_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___redArg();
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(lean_object* v_sep_1797_){
_start:
{
lean_object* v___f_1798_; 
v___f_1798_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___redArg___closed__0));
return v___f_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___boxed(lean_object* v_sep_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(v_sep_1799_);
lean_dec_ref(v_sep_1799_);
return v_res_1800_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default(void){
_start:
{
uint8_t v___x_1801_; 
v___x_1801_ = 0;
return v___x_1801_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited(void){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = 0;
return v___x_1802_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(uint8_t v_v_1811_, lean_object* v_x_1812_){
_start:
{
return v_v_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed(lean_object* v_v_1813_, lean_object* v_x_1814_){
_start:
{
uint8_t v_v_boxed_1815_; uint8_t v_res_1816_; lean_object* v_r_1817_; 
v_v_boxed_1815_ = lean_unbox(v_v_1813_);
v_res_1816_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(v_v_boxed_1815_, v_x_1814_);
lean_dec_ref(v_x_1814_);
v_r_1817_ = lean_box(v_res_1816_);
return v_r_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object* v_doc_1819_, uint8_t v_isBracketed_1820_){
_start:
{
lean_object* v___f_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___f_1821_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0));
v___x_1822_ = 0;
v___x_1823_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1824_ = lean_box(v___x_1822_);
v___x_1825_ = lean_box(v_isBracketed_1820_);
v___x_1826_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1824_, v___x_1823_, v_doc_1819_, v___x_1825_, v___f_1821_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___boxed(lean_object* v_doc_1827_, lean_object* v_isBracketed_1828_){
_start:
{
uint8_t v_isBracketed_boxed_1829_; lean_object* v_res_1830_; 
v_isBracketed_boxed_1829_ = lean_unbox(v_isBracketed_1828_);
v_res_1830_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_1827_, v_isBracketed_boxed_1829_);
return v_res_1830_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object* v_doc_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1833_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1832_, v_doc_1831_);
if (lean_obj_tag(v___x_1833_) == 0)
{
uint8_t v___x_1834_; 
v___x_1834_ = 0;
return v___x_1834_;
}
else
{
uint8_t v___x_1835_; 
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = 1;
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isSelfDelimited___boxed(lean_object* v_doc_1836_){
_start:
{
uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_res_1837_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1836_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object* v_doc_1839_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1841_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1840_, v_doc_1839_);
if (lean_obj_tag(v___x_1841_) == 0)
{
uint8_t v___x_1842_; 
v___x_1842_ = 0;
return v___x_1842_;
}
else
{
lean_object* v_val_1843_; uint8_t v___x_1844_; 
v_val_1843_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_val_1843_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1844_ = lean_unbox(v_val_1843_);
lean_dec(v_val_1843_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isBracketed___boxed(lean_object* v_doc_1845_){
_start:
{
uint8_t v_res_1846_; lean_object* v_r_1847_; 
v_res_1846_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_doc_1845_);
v_r_1847_ = lean_box(v_res_1846_);
return v_r_1847_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default(void){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_box(0);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback(void){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_box(0);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(lean_object* v_v_1858_, lean_object* v_x_1859_){
_start:
{
return v_v_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed(lean_object* v_v_1860_, lean_object* v_x_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(v_v_1860_, v_x_1861_);
lean_dec_ref(v_x_1861_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object* v_doc_1864_){
_start:
{
lean_object* v___f_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___f_1865_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0));
v___x_1866_ = lean_box(0);
v___x_1867_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1868_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1866_, v___x_1867_, v_doc_1864_, v___x_1866_, v___f_1865_);
return v___x_1868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object* v_doc_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1871_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1870_, v_doc_1869_);
if (lean_obj_tag(v___x_1871_) == 0)
{
uint8_t v___x_1872_; 
v___x_1872_ = 0;
return v___x_1872_;
}
else
{
uint8_t v___x_1873_; 
lean_dec_ref_known(v___x_1871_, 1);
v___x_1873_ = 1;
return v___x_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isRawFallback___boxed(lean_object* v_doc_1874_){
_start:
{
uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_res_1875_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1874_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default(void){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = lean_box(0);
return v___x_1877_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned(void){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_box(0);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0(lean_object* v_v_1887_, lean_object* v_x_1888_){
_start:
{
return v_v_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0___boxed(lean_object* v_v_1889_, lean_object* v_x_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0(v_v_1889_, v_x_1890_);
lean_dec_ref(v_x_1890_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object* v_doc_1893_){
_start:
{
lean_object* v___f_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___f_1894_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoAligned___closed__0));
v___x_1895_ = lean_box(0);
v___x_1896_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_));
v___x_1897_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1895_, v___x_1896_, v_doc_1893_, v___x_1895_, v___f_1894_);
return v___x_1897_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isPseudoAligned(lean_object* v_doc_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_));
v___x_1900_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1899_, v_doc_1898_);
if (lean_obj_tag(v___x_1900_) == 0)
{
uint8_t v___x_1901_; 
v___x_1901_ = 0;
return v___x_1901_;
}
else
{
uint8_t v___x_1902_; 
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = 1;
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isPseudoAligned___boxed(lean_object* v_doc_1903_){
_start:
{
uint8_t v_res_1904_; lean_object* v_r_1905_; 
v_res_1904_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_1903_);
v_r_1905_ = lean_box(v_res_1904_);
return v_r_1905_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object* v_doc_1906_){
_start:
{
uint8_t v___x_1907_; 
lean_inc_ref(v_doc_1906_);
v___x_1907_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1906_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_doc_1906_);
if (v___x_1908_ == 0)
{
uint8_t v___x_1909_; 
v___x_1909_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1906_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; 
v___x_1910_ = 1;
return v___x_1910_;
}
else
{
return v___x_1907_;
}
}
else
{
lean_dec_ref(v_doc_1906_);
return v___x_1907_;
}
}
else
{
lean_dec_ref(v_doc_1906_);
return v___x_1907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_needsAppBrackets___boxed(lean_object* v_doc_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_doc_1911_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default(void){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1914_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented(void){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object* v_indentedVariant_1925_, lean_object* v_dedentedVariant_1926_){
_start:
{
lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___f_1927_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0));
v___x_1928_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1929_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1930_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1928_, v___x_1929_, v_indentedVariant_1925_, v_dedentedVariant_1926_, v___f_1927_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object* v_doc_1931_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1933_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1932_, v_doc_1931_);
return v___x_1933_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_TaggedDoc_failure = _init_l_Lean_Fmt_TaggedDoc_failure();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_failure);
l_Lean_Fmt_TaggedDoc_nl = _init_l_Lean_Fmt_TaggedDoc_nl();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_nl);
l_Lean_Fmt_TaggedDoc_break = _init_l_Lean_Fmt_TaggedDoc_break();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_break);
l_Lean_Fmt_TaggedDoc_hardNl = _init_l_Lean_Fmt_TaggedDoc_hardNl();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_hardNl);
l_Lean_Fmt_TaggedDoc_empty = _init_l_Lean_Fmt_TaggedDoc_empty();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_empty);
l_Lean_Fmt_TaggedDoc_space = _init_l_Lean_Fmt_TaggedDoc_space();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_space);
l_Lean_Fmt_TaggedDoc_softSpace = _init_l_Lean_Fmt_TaggedDoc_softSpace();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_softSpace);
l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default();
l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind = _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind();
l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default);
l_Lean_Fmt_TaggedDoc_instInhabitedSticky = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedSticky);
l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default();
l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited = _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited();
l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default);
l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback = _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback);
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default);
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned);
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default);
l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented = _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented();
lean_mark_persistent(l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Attribute(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Attribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Primitives(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Fmt_Doc_hardNl(lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_break(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_empty(lean_object*);
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
lean_object* l_Lean_Fmt_Doc_nl(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object*);
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
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_nbuckets_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_120_ = lean_array_get_size(v_data_119_);
v___x_121_ = lean_unsigned_to_nat(2u);
v_nbuckets_122_ = lean_nat_mul(v___x_120_, v___x_121_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_box(0);
v___x_125_ = lean_mk_array(v_nbuckets_122_, v___x_124_);
v___x_126_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v___x_123_, v_data_119_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(lean_object* v_freshTagId_127_, uint8_t v_kind_128_, lean_object* v_m_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_size_131_; lean_object* v_buckets_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_184_; 
v_size_131_ = lean_ctor_get(v_m_129_, 0);
v_buckets_132_ = lean_ctor_get(v_m_129_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_m_129_);
if (v_isSharedCheck_184_ == 0)
{
v___x_134_ = v_m_129_;
v_isShared_135_ = v_isSharedCheck_184_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_buckets_132_);
lean_inc(v_size_131_);
lean_dec(v_m_129_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_184_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; uint64_t v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v_fold_140_; uint64_t v___x_141_; uint64_t v___x_142_; uint64_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; lean_object* v_bkt_149_; uint8_t v___x_150_; 
v___x_136_ = lean_array_get_size(v_buckets_132_);
v___x_137_ = l_Lean_Syntax_instHashableRange_hash(v_a_130_);
v___x_138_ = 32ULL;
v___x_139_ = lean_uint64_shift_right(v___x_137_, v___x_138_);
v_fold_140_ = lean_uint64_xor(v___x_137_, v___x_139_);
v___x_141_ = 16ULL;
v___x_142_ = lean_uint64_shift_right(v_fold_140_, v___x_141_);
v___x_143_ = lean_uint64_xor(v_fold_140_, v___x_142_);
v___x_144_ = lean_uint64_to_usize(v___x_143_);
v___x_145_ = lean_usize_of_nat(v___x_136_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v___x_145_, v___x_146_);
v___x_148_ = lean_usize_land(v___x_144_, v___x_147_);
v_bkt_149_ = lean_array_uget_borrowed(v_buckets_132_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_130_, v_bkt_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_size_x27_156_; lean_object* v___x_157_; lean_object* v_buckets_x27_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_mk_empty_array_with_capacity(v___x_151_);
v___x_153_ = lean_array_push(v___x_152_, v_freshTagId_127_);
v___x_154_ = lean_box(v_kind_128_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v_size_x27_156_ = lean_nat_add(v_size_131_, v___x_151_);
lean_dec(v_size_131_);
lean_inc(v_bkt_149_);
v___x_157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_157_, 0, v_a_130_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v_bkt_149_);
v_buckets_x27_158_ = lean_array_uset(v_buckets_132_, v___x_148_, v___x_157_);
v___x_159_ = lean_unsigned_to_nat(4u);
v___x_160_ = lean_nat_mul(v_size_x27_156_, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(3u);
v___x_162_ = lean_nat_div(v___x_160_, v___x_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_array_get_size(v_buckets_x27_158_);
v___x_164_ = lean_nat_dec_le(v___x_162_, v___x_163_);
lean_dec(v___x_162_);
if (v___x_164_ == 0)
{
lean_object* v_val_165_; lean_object* v___x_167_; 
v_val_165_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_buckets_x27_158_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_val_165_);
lean_ctor_set(v___x_134_, 0, v_size_x27_156_);
v___x_167_ = v___x_134_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_val_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
else
{
lean_object* v___x_170_; 
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v_buckets_x27_158_);
lean_ctor_set(v___x_134_, 0, v_size_x27_156_);
v___x_170_ = v___x_134_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_x27_156_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_buckets_x27_158_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
else
{
lean_object* v___x_172_; lean_object* v_buckets_x27_173_; lean_object* v_bkt_x27_174_; lean_object* v___y_176_; uint8_t v___x_181_; 
lean_inc(v_bkt_149_);
v___x_172_ = lean_box(0);
v_buckets_x27_173_ = lean_array_uset(v_buckets_132_, v___x_148_, v___x_172_);
lean_inc_ref(v_a_130_);
v_bkt_x27_174_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__2(v_freshTagId_127_, v_kind_128_, v_a_130_, v_bkt_149_);
v___x_181_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_130_, v_bkt_x27_174_);
lean_dec_ref(v_a_130_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_sub(v_size_131_, v___x_182_);
lean_dec(v_size_131_);
v___y_176_ = v___x_183_;
goto v___jp_175_;
}
else
{
v___y_176_ = v_size_131_;
goto v___jp_175_;
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_array_uset(v_buckets_x27_173_, v___x_148_, v_bkt_x27_174_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_177_);
lean_ctor_set(v___x_134_, 0, v___y_176_);
v___x_179_ = v___x_134_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___y_176_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0___boxed(lean_object* v_freshTagId_185_, lean_object* v_kind_186_, lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
uint8_t v_kind_boxed_189_; lean_object* v_res_190_; 
v_kind_boxed_189_ = lean_unbox(v_kind_186_);
v_res_190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_185_, v_kind_boxed_189_, v_m_187_, v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange(lean_object* v_freshTagId_191_, lean_object* v_tags_192_, lean_object* v_doc_193_, lean_object* v_range_194_, uint8_t v_kind_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_doc_198_; lean_object* v_tags_199_; lean_object* v___x_200_; lean_object* v_freshTagId_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_inc_n(v_freshTagId_191_, 2);
v___x_196_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_freshTagId_191_, v_doc_193_);
v___x_197_ = lean_box(0);
v_doc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_doc_198_, 0, v___x_196_);
lean_ctor_set(v_doc_198_, 1, v___x_197_);
v_tags_199_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0(v_freshTagId_191_, v_kind_195_, v_tags_192_, v_range_194_);
v___x_200_ = lean_unsigned_to_nat(1u);
v_freshTagId_201_ = lean_nat_add(v_freshTagId_191_, v___x_200_);
lean_dec(v_freshTagId_191_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_tags_199_);
lean_ctor_set(v___x_202_, 1, v_doc_198_);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_freshTagId_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWithRange___boxed(lean_object* v_freshTagId_204_, lean_object* v_tags_205_, lean_object* v_doc_206_, lean_object* v_range_207_, lean_object* v_kind_208_){
_start:
{
uint8_t v_kind_boxed_209_; lean_object* v_res_210_; 
v_kind_boxed_209_ = lean_unbox(v_kind_208_);
v_res_210_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_204_, v_tags_205_, v_doc_206_, v_range_207_, v_kind_boxed_209_);
return v_res_210_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(lean_object* v_00_u03b2_211_, lean_object* v_a_212_, lean_object* v_x_213_){
_start:
{
uint8_t v___x_214_; 
v___x_214_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___redArg(v_a_212_, v_x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0___boxed(lean_object* v_00_u03b2_215_, lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_res_218_; lean_object* v_r_219_; 
v_res_218_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__0(v_00_u03b2_215_, v_a_216_, v_x_217_);
lean_dec(v_x_217_);
lean_dec_ref(v_a_216_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1(lean_object* v_00_u03b2_220_, lean_object* v_data_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1___redArg(v_data_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_223_, lean_object* v_i_224_, lean_object* v_source_225_, lean_object* v_target_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2___redArg(v_i_224_, v_source_225_, v_target_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_Fmt_TaggedDoc_taggedWithRange_spec__0_spec__1_spec__2_spec__3___redArg(v_x_229_, v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg(lean_object* v_doc_232_, lean_object* v_ref_233_, lean_object* v_a_234_){
_start:
{
uint8_t v___x_235_; lean_object* v___x_236_; 
v___x_235_ = 0;
v___x_236_ = l_Lean_Syntax_getRange_x3f(v_ref_233_, v___x_235_);
if (lean_obj_tag(v___x_236_) == 1)
{
lean_object* v_val_237_; lean_object* v_toBacktrackableState_238_; lean_object* v_shareCommonState_239_; lean_object* v_freshTagId_240_; lean_object* v_missingFormatters_241_; lean_object* v_partialFormatters_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_262_; 
v_val_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_236_, 1);
v_toBacktrackableState_238_ = lean_ctor_get(v_a_234_, 0);
v_shareCommonState_239_ = lean_ctor_get(v_a_234_, 1);
v_freshTagId_240_ = lean_ctor_get(v_a_234_, 2);
v_missingFormatters_241_ = lean_ctor_get(v_a_234_, 3);
v_partialFormatters_242_ = lean_ctor_get(v_a_234_, 4);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_234_);
if (v_isSharedCheck_262_ == 0)
{
v___x_244_ = v_a_234_;
v_isShared_245_ = v_isSharedCheck_262_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_partialFormatters_242_);
lean_inc(v_missingFormatters_241_);
lean_inc(v_freshTagId_240_);
lean_inc(v_shareCommonState_239_);
lean_inc(v_toBacktrackableState_238_);
lean_dec(v_a_234_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_262_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v_snd_248_; lean_object* v_fst_249_; lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_261_; 
v___x_246_ = 2;
v___x_247_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_240_, v_toBacktrackableState_238_, v_doc_232_, v_val_237_, v___x_246_);
v_snd_248_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_snd_248_);
v_fst_249_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_fst_249_);
lean_dec_ref(v___x_247_);
v_fst_250_ = lean_ctor_get(v_snd_248_, 0);
v_snd_251_ = lean_ctor_get(v_snd_248_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_snd_248_);
if (v_isSharedCheck_261_ == 0)
{
v___x_253_ = v_snd_248_;
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_snd_251_);
lean_inc(v_fst_250_);
lean_dec(v_snd_248_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 2, v_fst_249_);
lean_ctor_set(v___x_244_, 0, v_fst_250_);
v___x_256_ = v___x_244_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_fst_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_shareCommonState_239_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_fst_249_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_missingFormatters_241_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_partialFormatters_242_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v___x_256_);
lean_ctor_set(v___x_253_, 0, v_snd_251_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_snd_251_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v___x_236_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_doc_232_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_a_234_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___redArg___boxed(lean_object* v_doc_266_, lean_object* v_ref_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_266_, v_ref_267_, v_a_268_);
lean_dec(v_ref_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText(lean_object* v_doc_270_, lean_object* v_ref_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v_doc_270_, v_ref_271_, v_a_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedText___boxed(lean_object* v_doc_275_, lean_object* v_ref_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Fmt_TaggedDoc_taggedText(v_doc_275_, v_ref_276_, v_a_277_, v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_ref_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg(lean_object* v_doc_280_, lean_object* v_ref_281_, lean_object* v_a_282_){
_start:
{
uint8_t v___x_283_; lean_object* v___x_284_; 
v___x_283_ = 0;
v___x_284_ = l_Lean_Syntax_getRange_x3f(v_ref_281_, v___x_283_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; lean_object* v_toBacktrackableState_286_; lean_object* v_shareCommonState_287_; lean_object* v_freshTagId_288_; lean_object* v_missingFormatters_289_; lean_object* v_partialFormatters_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_310_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_284_, 1);
v_toBacktrackableState_286_ = lean_ctor_get(v_a_282_, 0);
v_shareCommonState_287_ = lean_ctor_get(v_a_282_, 1);
v_freshTagId_288_ = lean_ctor_get(v_a_282_, 2);
v_missingFormatters_289_ = lean_ctor_get(v_a_282_, 3);
v_partialFormatters_290_ = lean_ctor_get(v_a_282_, 4);
v_isSharedCheck_310_ = !lean_is_exclusive(v_a_282_);
if (v_isSharedCheck_310_ == 0)
{
v___x_292_ = v_a_282_;
v_isShared_293_ = v_isSharedCheck_310_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_partialFormatters_290_);
lean_inc(v_missingFormatters_289_);
lean_inc(v_freshTagId_288_);
lean_inc(v_shareCommonState_287_);
lean_inc(v_toBacktrackableState_286_);
lean_dec(v_a_282_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_310_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v_snd_296_; lean_object* v_fst_297_; lean_object* v_fst_298_; lean_object* v_snd_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_309_; 
v___x_294_ = 1;
v___x_295_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_288_, v_toBacktrackableState_286_, v_doc_280_, v_val_285_, v___x_294_);
v_snd_296_ = lean_ctor_get(v___x_295_, 1);
lean_inc(v_snd_296_);
v_fst_297_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_fst_297_);
lean_dec_ref(v___x_295_);
v_fst_298_ = lean_ctor_get(v_snd_296_, 0);
v_snd_299_ = lean_ctor_get(v_snd_296_, 1);
v_isSharedCheck_309_ = !lean_is_exclusive(v_snd_296_);
if (v_isSharedCheck_309_ == 0)
{
v___x_301_ = v_snd_296_;
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_snd_299_);
lean_inc(v_fst_298_);
lean_dec(v_snd_296_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 2, v_fst_297_);
lean_ctor_set(v___x_292_, 0, v_fst_298_);
v___x_304_ = v___x_292_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_fst_298_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_shareCommonState_287_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_fst_297_);
lean_ctor_set(v_reuseFailAlloc_308_, 3, v_missingFormatters_289_);
lean_ctor_set(v_reuseFailAlloc_308_, 4, v_partialFormatters_290_);
v___x_304_ = v_reuseFailAlloc_308_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
lean_object* v___x_306_; 
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 1, v___x_304_);
lean_ctor_set(v___x_301_, 0, v_snd_299_);
v___x_306_ = v___x_301_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_snd_299_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v___x_284_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_312_, 0, v_doc_280_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v_a_282_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___redArg___boxed(lean_object* v_doc_314_, lean_object* v_ref_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_314_, v_ref_315_, v_a_316_);
lean_dec(v_ref_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode(lean_object* v_doc_318_, lean_object* v_ref_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_318_, v_ref_319_, v_a_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedNode___boxed(lean_object* v_doc_323_, lean_object* v_ref_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Fmt_TaggedDoc_taggedNode(v_doc_323_, v_ref_324_, v_a_325_, v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_ref_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(lean_object* v_doc_328_, lean_object* v_range_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_toBacktrackableState_331_; lean_object* v_shareCommonState_332_; lean_object* v_freshTagId_333_; lean_object* v_missingFormatters_334_; lean_object* v_partialFormatters_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_355_; 
v_toBacktrackableState_331_ = lean_ctor_get(v_a_330_, 0);
v_shareCommonState_332_ = lean_ctor_get(v_a_330_, 1);
v_freshTagId_333_ = lean_ctor_get(v_a_330_, 2);
v_missingFormatters_334_ = lean_ctor_get(v_a_330_, 3);
v_partialFormatters_335_ = lean_ctor_get(v_a_330_, 4);
v_isSharedCheck_355_ = !lean_is_exclusive(v_a_330_);
if (v_isSharedCheck_355_ == 0)
{
v___x_337_ = v_a_330_;
v_isShared_338_ = v_isSharedCheck_355_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_partialFormatters_335_);
lean_inc(v_missingFormatters_334_);
lean_inc(v_freshTagId_333_);
lean_inc(v_shareCommonState_332_);
lean_inc(v_toBacktrackableState_331_);
lean_dec(v_a_330_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_355_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v_snd_341_; lean_object* v_fst_342_; lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_354_; 
v___x_339_ = 0;
v___x_340_ = l_Lean_Fmt_TaggedDoc_taggedWithRange(v_freshTagId_333_, v_toBacktrackableState_331_, v_doc_328_, v_range_329_, v___x_339_);
v_snd_341_ = lean_ctor_get(v___x_340_, 1);
lean_inc(v_snd_341_);
v_fst_342_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_fst_342_);
lean_dec_ref(v___x_340_);
v_fst_343_ = lean_ctor_get(v_snd_341_, 0);
v_snd_344_ = lean_ctor_get(v_snd_341_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_snd_341_);
if (v_isSharedCheck_354_ == 0)
{
v___x_346_ = v_snd_341_;
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_inc(v_fst_343_);
lean_dec(v_snd_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_354_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 2, v_fst_342_);
lean_ctor_set(v___x_337_, 0, v_fst_343_);
v___x_349_ = v___x_337_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_fst_343_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_shareCommonState_332_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_fst_342_);
lean_ctor_set(v_reuseFailAlloc_353_, 3, v_missingFormatters_334_);
lean_ctor_set(v_reuseFailAlloc_353_, 4, v_partialFormatters_335_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_349_);
lean_ctor_set(v___x_346_, 0, v_snd_344_);
v___x_351_ = v___x_346_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_snd_344_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_349_);
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
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace(lean_object* v_doc_356_, lean_object* v_range_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace___redArg(v_doc_356_, v_range_357_, v_a_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_taggedWhitespace___boxed(lean_object* v_doc_361_, lean_object* v_range_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Fmt_TaggedDoc_taggedWhitespace(v_doc_361_, v_range_362_, v_a_363_, v_a_364_);
lean_dec_ref(v_a_363_);
return v_res_365_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isTagged(lean_object* v_d_366_){
_start:
{
lean_object* v_doc_367_; 
v_doc_367_ = lean_ctor_get(v_d_366_, 0);
if (lean_obj_tag(v_doc_367_) == 3)
{
uint8_t v___x_368_; 
v___x_368_ = 1;
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
v___x_369_ = 0;
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isTagged___boxed(lean_object* v_d_370_){
_start:
{
uint8_t v_res_371_; lean_object* v_r_372_; 
v_res_371_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_370_);
lean_dec_ref(v_d_370_);
v_r_372_ = lean_box(v_res_371_);
return v_r_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg(lean_object* v_d_373_, lean_object* v_ref_374_, lean_object* v_a_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = l_Lean_Fmt_TaggedDoc_isTagged(v_d_373_);
if (v___x_376_ == 0)
{
lean_object* v_doc_377_; lean_object* v_metaData_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_397_; 
v_doc_377_ = lean_ctor_get(v_d_373_, 0);
lean_inc(v_doc_377_);
v_metaData_378_ = lean_ctor_get(v_d_373_, 1);
lean_inc(v_metaData_378_);
lean_dec_ref(v_d_373_);
v___x_379_ = l_Lean_Fmt_TaggedDoc_taggedNode___redArg(v_doc_377_, v_ref_374_, v_a_375_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_a_381_ = lean_ctor_get(v___x_379_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_397_ == 0)
{
v___x_383_ = v___x_379_;
v_isShared_384_ = v_isSharedCheck_397_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_397_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_doc_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_395_; 
v_doc_385_ = lean_ctor_get(v_a_380_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v_a_380_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v_a_380_, 1);
lean_dec(v_unused_396_);
v___x_387_ = v_a_380_;
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_doc_385_);
lean_dec(v_a_380_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_metaData_378_);
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_doc_385_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_metaData_378_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_392_; 
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_390_);
v___x_392_ = v___x_383_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_a_381_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_d_373_);
lean_ctor_set(v___x_398_, 1, v_a_375_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___redArg___boxed(lean_object* v_d_399_, lean_object* v_ref_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_399_, v_ref_400_, v_a_401_);
lean_dec(v_ref_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag(lean_object* v_d_403_, lean_object* v_ref_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Fmt_TaggedDoc_tag___redArg(v_d_403_, v_ref_404_, v_a_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_tag___boxed(lean_object* v_d_408_, lean_object* v_ref_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Fmt_TaggedDoc_tag(v_d_408_, v_ref_409_, v_a_410_, v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_ref_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(lean_object* v_inst_413_, lean_object* v_x_414_){
_start:
{
lean_object* v_v_415_; lean_object* v___x_416_; 
v_v_415_ = lean_ctor_get(v_x_414_, 0);
v___x_416_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_415_, v_inst_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed(lean_object* v_inst_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0(v_inst_417_, v_x_418_);
lean_dec_ref(v_x_418_);
lean_dec(v_inst_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(lean_object* v_inst_420_, lean_object* v_d_421_){
_start:
{
lean_object* v_metaData_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
v_metaData_422_ = lean_ctor_get(v_d_421_, 1);
lean_inc(v_metaData_422_);
lean_dec_ref(v_d_421_);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_423_, 0, v_inst_420_);
v___x_424_ = l_List_findSome_x3f___redArg(v___f_423_, v_metaData_422_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getMetaData_x3f(lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_d_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v_inst_426_, v_d_427_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__2));
v___x_433_ = lean_unsigned_to_nat(14u);
v___x_434_ = lean_unsigned_to_nat(22u);
v___x_435_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__1));
v___x_436_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__0));
v___x_437_ = l_mkPanicMessageWithDecl(v___x_436_, v___x_435_, v___x_434_, v___x_433_, v___x_432_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_propagate_440_, lean_object* v_v_441_, lean_object* v_f_442_){
_start:
{
lean_object* v___y_444_; lean_object* v___x_447_; 
v___x_447_ = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(v_v_441_, v_inst_439_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3, &l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___closed__3);
v___x_449_ = l_panic___redArg(v_inst_438_, v___x_448_);
v___y_444_ = v___x_449_;
goto v___jp_443_;
}
else
{
lean_object* v_val_450_; 
v_val_450_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_447_, 1);
v___y_444_ = v_val_450_;
goto v___jp_443_;
}
v___jp_443_:
{
lean_object* v_r_445_; lean_object* v___x_446_; 
v_r_445_ = lean_apply_2(v_propagate_440_, v___y_444_, v_f_442_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_inst_439_);
lean_ctor_set(v___x_446_, 1, v_r_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg___boxed(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_propagate_453_, lean_object* v_v_454_, lean_object* v_f_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_451_, v_inst_452_, v_propagate_453_, v_v_454_, v_f_455_);
lean_dec(v_v_454_);
lean_dec(v_inst_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(lean_object* v_00_u03b1_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_propagate_460_, lean_object* v_v_461_, lean_object* v_f_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___redArg(v_inst_458_, v_inst_459_, v_propagate_460_, v_v_461_, v_f_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed(lean_object* v_00_u03b1_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_propagate_467_, lean_object* v_v_468_, lean_object* v_f_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic(v_00_u03b1_464_, v_inst_465_, v_inst_466_, v_propagate_467_, v_v_468_, v_f_469_);
lean_dec(v_v_468_);
lean_dec(v_inst_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData___redArg(lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_d_473_, lean_object* v_metaData_474_, lean_object* v_propagate_475_){
_start:
{
lean_object* v_doc_476_; lean_object* v_metaData_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_488_; 
v_doc_476_ = lean_ctor_get(v_d_473_, 0);
v_metaData_477_ = lean_ctor_get(v_d_473_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_d_473_);
if (v_isSharedCheck_488_ == 0)
{
v___x_479_ = v_d_473_;
v_isShared_480_ = v_isSharedCheck_488_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_metaData_477_);
lean_inc(v_doc_476_);
lean_dec(v_d_473_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_488_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
lean_inc(v_inst_472_);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v_inst_472_);
lean_ctor_set(v___x_481_, 1, v_metaData_474_);
v___x_482_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_addMetaData_propagateDynamic___boxed), 6, 4);
lean_closure_set(v___x_482_, 0, lean_box(0));
lean_closure_set(v___x_482_, 1, v_inst_471_);
lean_closure_set(v___x_482_, 2, v_inst_472_);
lean_closure_set(v___x_482_, 3, v_propagate_475_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_metaData_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_484_);
v___x_486_ = v___x_479_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_doc_476_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_addMetaData(lean_object* v_00_u03b1_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_d_492_, lean_object* v_metaData_493_, lean_object* v_propagate_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v_inst_490_, v_inst_491_, v_d_492_, v_metaData_493_, v_propagate_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(lean_object* v_f_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
if (lean_obj_tag(v_a_497_) == 0)
{
lean_object* v___x_499_; 
lean_dec_ref(v_f_496_);
v___x_499_ = l_List_reverse___redArg(v_a_498_);
return v___x_499_;
}
else
{
lean_object* v_head_500_; lean_object* v_tail_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_519_; 
v_head_500_ = lean_ctor_get(v_a_497_, 0);
v_tail_501_ = lean_ctor_get(v_a_497_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_519_ == 0)
{
v___x_503_ = v_a_497_;
v_isShared_504_ = v_isSharedCheck_519_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_tail_501_);
lean_inc(v_head_500_);
lean_dec(v_a_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_519_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v_v_505_; lean_object* v_propagate_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_518_; 
v_v_505_ = lean_ctor_get(v_head_500_, 0);
v_propagate_506_ = lean_ctor_get(v_head_500_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_head_500_);
if (v_isSharedCheck_518_ == 0)
{
v___x_508_ = v_head_500_;
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_propagate_506_);
lean_inc(v_v_505_);
lean_dec(v_head_500_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
lean_inc(v_propagate_506_);
lean_inc_ref(v_f_496_);
v___x_510_ = lean_apply_2(v_propagate_506_, v_v_505_, v_f_496_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_propagate_506_);
v___x_512_ = v_reuseFailAlloc_517_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_a_498_);
lean_ctor_set(v___x_503_, 0, v___x_512_);
v___x_514_ = v___x_503_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_a_498_);
v___x_514_ = v_reuseFailAlloc_516_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
v_a_497_ = v_tail_501_;
v_a_498_ = v___x_514_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateMetaData(lean_object* v_d_520_, lean_object* v_f_521_){
_start:
{
lean_object* v_doc_522_; lean_object* v_metaData_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_533_; 
v_doc_522_ = lean_ctor_get(v_d_520_, 0);
v_metaData_523_ = lean_ctor_get(v_d_520_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_d_520_);
if (v_isSharedCheck_533_ == 0)
{
v___x_525_ = v_d_520_;
v_isShared_526_ = v_isSharedCheck_533_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_metaData_523_);
lean_inc(v_doc_522_);
lean_dec(v_d_520_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_533_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_inc_ref(v_f_521_);
v___x_527_ = lean_apply_1(v_f_521_, v_doc_522_);
v___x_528_ = lean_box(0);
v___x_529_ = l_List_mapTR_loop___at___00Lean_Fmt_TaggedDoc_propagateMetaData_spec__0(v_f_521_, v_metaData_523_, v___x_528_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___x_529_);
lean_ctor_set(v___x_525_, 0, v___x_527_);
v___x_531_ = v___x_525_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(size_t v_sz_534_, size_t v_i_535_, lean_object* v_bs_536_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = lean_usize_dec_lt(v_i_535_, v_sz_534_);
if (v___x_537_ == 0)
{
return v_bs_536_;
}
else
{
lean_object* v_v_538_; lean_object* v_doc_539_; lean_object* v___x_540_; lean_object* v_bs_x27_541_; size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v_v_538_ = lean_array_uget_borrowed(v_bs_536_, v_i_535_);
v_doc_539_ = lean_ctor_get(v_v_538_, 0);
lean_inc(v_doc_539_);
v___x_540_ = lean_unsigned_to_nat(0u);
v_bs_x27_541_ = lean_array_uset(v_bs_536_, v_i_535_, v___x_540_);
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_add(v_i_535_, v___x_542_);
v___x_544_ = lean_array_uset(v_bs_x27_541_, v_i_535_, v_doc_539_);
v_i_535_ = v___x_543_;
v_bs_536_ = v___x_544_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0___boxed(lean_object* v_sz_546_, lean_object* v_i_547_, lean_object* v_bs_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_546_);
lean_dec(v_sz_546_);
v_i_boxed_550_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_boxed_549_, v_i_boxed_550_, v_bs_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(lean_object* v_ds_552_, lean_object* v_f_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_array_get_size(v_ds_552_);
v___x_555_ = lean_unsigned_to_nat(1u);
v___x_556_ = lean_nat_dec_eq(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
size_t v_sz_557_; size_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_sz_557_ = lean_array_size(v_ds_552_);
v___x_558_ = ((size_t)0ULL);
v___x_559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_557_, v___x_558_, v_ds_552_);
v___x_560_ = lean_apply_1(v_f_553_, v___x_559_);
v___x_561_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_560_);
return v___x_561_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_f_553_);
v___x_562_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_array_get(v___x_562_, v_ds_552_, v___x_563_);
lean_dec_ref(v_ds_552_);
return v___x_564_;
}
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure___closed__0(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_box(0);
v___x_566_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_failure(void){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_failure___closed__0, &l_Lean_Fmt_TaggedDoc_failure___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_failure___closed__0);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_newline(lean_object* v_flattened_568_){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = l_Lean_Fmt_Doc_newline___override___redArg(v_flattened_568_);
v___x_570_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__0(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Fmt_Doc_nl(lean_box(0));
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__0, &l_Lean_Fmt_TaggedDoc_nl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__0);
v___x_573_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_nl(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_nl___closed__1, &l_Lean_Fmt_TaggedDoc_nl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_nl___closed__1);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__0(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Fmt_Doc_break(lean_box(0));
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break___closed__1(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__0, &l_Lean_Fmt_TaggedDoc_break___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__0);
v___x_577_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_break(void){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_break___closed__1, &l_Lean_Fmt_TaggedDoc_break___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_break___closed__1);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Fmt_Doc_hardNl(lean_box(0));
return v___x_579_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__0, &l_Lean_Fmt_TaggedDoc_hardNl___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__0);
v___x_581_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_hardNl(void){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_hardNl___closed__1, &l_Lean_Fmt_TaggedDoc_hardNl___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_hardNl___closed__1);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg(lean_object* v_s_583_, lean_object* v_ref_584_, lean_object* v_a_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_583_);
v___x_587_ = l_Lean_Fmt_TaggedDoc_taggedText___redArg(v___x_586_, v_ref_584_, v_a_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___redArg___boxed(lean_object* v_s_588_, lean_object* v_ref_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_588_, v_ref_589_, v_a_590_);
lean_dec(v_ref_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text(lean_object* v_s_592_, lean_object* v_ref_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Fmt_TaggedDoc_text___redArg(v_s_592_, v_ref_593_, v_a_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_text___boxed(lean_object* v_s_597_, lean_object* v_ref_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Fmt_TaggedDoc_text(v_s_597_, v_ref_598_, v_a_599_, v_a_600_);
lean_dec_ref(v_a_599_);
lean_dec(v_ref_598_);
return v_res_601_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__0(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Fmt_Doc_empty(lean_box(0));
return v___x_602_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__0, &l_Lean_Fmt_TaggedDoc_empty___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__0);
v___x_604_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_603_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_empty(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_empty___closed__1, &l_Lean_Fmt_TaggedDoc_empty___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_empty___closed__1);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__1(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_space___closed__0));
v___x_608_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space___closed__2(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__1, &l_Lean_Fmt_TaggedDoc_space___closed__1_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__1);
v___x_610_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_space(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_space___closed__2, &l_Lean_Fmt_TaggedDoc_space___closed__2_once, _init_l_Lean_Fmt_TaggedDoc_space___closed__2);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object* v_d_613_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_nested___closed__0));
v___x_615_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_613_, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object* v_d_617_){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_hardNested___closed__0));
v___x_619_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_617_, v___x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_doublyNested(lean_object* v_d_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = l_Lean_Fmt_TaggedDoc_nested(v_d_620_);
v___x_622_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object* v_d_623_){
_start:
{
lean_object* v_doc_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_doc_624_ = lean_ctor_get(v_d_623_, 0);
lean_inc(v_doc_624_);
lean_dec_ref(v_d_623_);
v___x_625_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_doc_624_);
v___x_626_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object* v_d_628_){
_start:
{
lean_object* v___f_629_; lean_object* v___x_630_; 
v___f_629_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_unflattenable___closed__0));
v___x_630_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_628_, v___f_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object* v_d_632_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_634_; 
v___f_633_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_flattened___closed__0));
v___x_634_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_632_, v___f_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object* v_d_636_){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_maybeFlattened___closed__0));
v___x_638_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_636_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0(uint8_t v_onlyNonCumulative_639_, lean_object* v_d_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_639_, v_d_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed(lean_object* v_onlyNonCumulative_642_, lean_object* v_d_643_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_644_; lean_object* v_res_645_; 
v_onlyNonCumulative_boxed_644_ = lean_unbox(v_onlyNonCumulative_642_);
v_res_645_ = l_Lean_Fmt_TaggedDoc_unindented___lam__0(v_onlyNonCumulative_boxed_644_, v_d_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object* v_d_646_, uint8_t v_onlyNonCumulative_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; 
v___x_648_ = lean_box(v_onlyNonCumulative_647_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_unindented___lam__0___boxed), 2, 1);
lean_closure_set(v___f_649_, 0, v___x_648_);
v___x_650_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_646_, v___f_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_unindented___boxed(lean_object* v_d_651_, lean_object* v_onlyNonCumulative_652_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_653_; lean_object* v_res_654_; 
v_onlyNonCumulative_boxed_653_ = lean_unbox(v_onlyNonCumulative_652_);
v_res_654_ = l_Lean_Fmt_TaggedDoc_unindented(v_d_651_, v_onlyNonCumulative_boxed_653_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_final(lean_object* v_d_656_){
_start:
{
lean_object* v___f_657_; lean_object* v___x_658_; 
v___f_657_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_final___closed__0));
v___x_658_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_656_, v___f_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_initial(lean_object* v_d_660_){
_start:
{
lean_object* v___f_661_; lean_object* v___x_662_; 
v___f_661_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_initial___closed__0));
v___x_662_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_660_, v___f_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object* v_d_664_){
_start:
{
lean_object* v___f_665_; lean_object* v___x_666_; 
v___f_665_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_free___closed__0));
v___x_666_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_664_, v___f_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded___lam__0(lean_object* v_p_667_, lean_object* v_d_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_667_, v_d_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object* v_p_670_, lean_object* v_d_671_){
_start:
{
lean_object* v___f_672_; lean_object* v___x_673_; 
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_guarded___lam__0), 2, 1);
lean_closure_set(v___f_672_, 0, v_p_670_);
v___x_673_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_671_, v___f_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0(lean_object* v_amount_674_, lean_object* v_d_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = l_Lean_Fmt_DefaultCost_ofFailureFallbackPenalty___redArg(v_amount_674_);
v___x_677_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_676_, v_d_675_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(lean_object* v_d_678_, lean_object* v_amount_679_){
_start:
{
lean_object* v___f_680_; lean_object* v___x_681_; 
v___f_680_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_680_, 0, v_amount_679_);
v___x_681_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_678_, v___f_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0(lean_object* v_amount_682_, lean_object* v_d_683_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = l_Lean_Fmt_DefaultCost_ofOverflowFallbackPenalty___redArg(v_amount_682_);
v___x_685_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_684_, v_d_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(lean_object* v_d_686_, lean_object* v_amount_687_){
_start:
{
lean_object* v___f_688_; lean_object* v___x_689_; 
v___f_688_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_688_, 0, v_amount_687_);
v___x_689_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_686_, v___f_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0(lean_object* v_amount_690_, lean_object* v_d_691_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v_amount_690_);
v___x_693_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_692_, v_d_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(lean_object* v_d_694_, lean_object* v_amount_695_){
_start:
{
lean_object* v___f_696_; lean_object* v___x_697_; 
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_696_, 0, v_amount_695_);
v___x_697_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_694_, v___f_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_either(lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
lean_object* v_doc_700_; lean_object* v_doc_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_doc_700_ = lean_ctor_get(v_a_698_, 0);
lean_inc(v_doc_700_);
lean_dec_ref(v_a_698_);
v_doc_701_ = lean_ctor_get(v_b_699_, 0);
lean_inc(v_doc_701_);
lean_dec_ref(v_b_699_);
v___x_702_ = l_Lean_Fmt_Doc_either___override___redArg(v_doc_700_, v_doc_701_);
v___x_703_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object* v_ds_705_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_707_; 
v___f_706_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_oneOf___closed__0));
v___x_707_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_705_, v___f_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnFailure(lean_object* v_d_708_, lean_object* v_fallback_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_710_ = lean_unsigned_to_nat(1u);
v___x_711_ = l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(v_fallback_709_, v___x_710_);
v___x_712_ = lean_unsigned_to_nat(2u);
v___x_713_ = lean_mk_empty_array_with_capacity(v___x_712_);
v___x_714_ = lean_array_push(v___x_713_, v_d_708_);
v___x_715_ = lean_array_push(v___x_714_, v___x_711_);
v___x_716_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object* v_d_717_, lean_object* v_fallback_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_fallback_718_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(2u);
v___x_722_ = lean_mk_empty_array_with_capacity(v___x_721_);
v___x_723_ = lean_array_push(v___x_722_, v_d_717_);
v___x_724_ = lean_array_push(v___x_723_, v___x_720_);
v___x_725_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object* v_d_726_, lean_object* v_fallback_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v_fallback_727_, v___x_728_);
v___x_730_ = lean_unsigned_to_nat(2u);
v___x_731_ = lean_mk_empty_array_with_capacity(v___x_730_);
v___x_732_ = lean_array_push(v___x_731_, v_d_726_);
v___x_733_ = lean_array_push(v___x_732_, v___x_729_);
v___x_734_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_733_);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_736_ = l_Lean_Fmt_TaggedDoc_space;
v___x_737_ = l_Lean_Fmt_TaggedDoc_fallbackOnFailure(v___x_736_, v___x_735_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_softSpace(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_softSpace___closed__0, &l_Lean_Fmt_TaggedDoc_softSpace___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_softSpace___closed__0);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object* v_a_739_, lean_object* v_b_740_){
_start:
{
lean_object* v_doc_741_; lean_object* v_doc_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_doc_741_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_doc_741_);
lean_dec_ref(v_a_739_);
v_doc_742_ = lean_ctor_get(v_b_740_, 0);
lean_inc(v_doc_742_);
lean_dec_ref(v_b_740_);
v___x_743_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_741_, v_doc_742_);
v___x_744_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object* v_ds_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; 
v___f_747_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_join___closed__0));
v___x_748_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_746_, v___f_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing___lam__0(lean_object* v_sep_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_doc_751_; lean_object* v___x_752_; 
v_doc_751_ = lean_ctor_get(v_sep_749_, 0);
lean_inc(v_doc_751_);
lean_dec_ref(v_sep_749_);
v___x_752_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_doc_751_, v_x_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object* v_sep_753_, lean_object* v_ds_754_){
_start:
{
lean_object* v___f_755_; lean_object* v___x_756_; 
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_joinUsing___lam__0), 2, 1);
lean_closure_set(v___f_755_, 0, v_sep_753_);
v___x_756_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_754_, v___f_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object* v_ds_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; 
v___f_759_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fill___closed__0));
v___x_760_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_758_, v___f_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0(lean_object* v_wrap_761_, lean_object* v_d_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_doc_765_; 
v___x_763_ = l_Lean_Fmt_TaggedDoc_untagged(v_d_762_);
v___x_764_ = lean_apply_1(v_wrap_761_, v___x_763_);
v_doc_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_doc_765_);
lean_dec_ref(v___x_764_);
return v_doc_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1(lean_object* v___f_766_, lean_object* v_x_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_x_767_, v___f_766_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object* v_ds_769_, lean_object* v_wrap_770_){
_start:
{
lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___x_773_; 
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_771_, 0, v_wrap_770_);
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1), 2, 1);
lean_closure_set(v___f_772_, 0, v___f_771_);
v___x_773_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_769_, v___f_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing___lam__0(lean_object* v_sep_774_, lean_object* v_x_775_){
_start:
{
lean_object* v_doc_776_; lean_object* v___x_777_; 
v_doc_776_ = lean_ctor_get(v_sep_774_, 0);
lean_inc(v_doc_776_);
lean_dec_ref(v_sep_774_);
v___x_777_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_doc_776_, v_x_775_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing(lean_object* v_sep_778_, lean_object* v_ds_779_){
_start:
{
lean_object* v___f_780_; lean_object* v___x_781_; 
v___f_780_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsing___lam__0), 2, 1);
lean_closure_set(v___f_780_, 0, v_sep_778_);
v___x_781_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_779_, v___f_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object* v_ds_783_){
_start:
{
lean_object* v___f_784_; lean_object* v___x_785_; 
v___f_784_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0));
v___x_785_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_783_, v___f_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1(lean_object* v___f_786_, lean_object* v_x_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_x_787_, v___f_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object* v_ds_789_, lean_object* v_wrap_790_){
_start:
{
lean_object* v___f_791_; lean_object* v___f_792_; lean_object* v___x_793_; 
v___f_791_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_791_, 0, v_wrap_790_);
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1), 2, 1);
lean_closure_set(v___f_792_, 0, v___f_791_);
v___x_793_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_789_, v___f_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_as_794_, size_t v_i_795_, size_t v_stop_796_, lean_object* v_b_797_){
_start:
{
uint8_t v___x_798_; 
v___x_798_ = lean_usize_dec_eq(v_i_795_, v_stop_796_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; size_t v___x_801_; size_t v___x_802_; 
v___x_799_ = lean_array_uget_borrowed(v_as_794_, v_i_795_);
v___x_800_ = l_Array_append___redArg(v_b_797_, v___x_799_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_795_, v___x_801_);
v_i_795_ = v___x_802_;
v_b_797_ = v___x_800_;
goto _start;
}
else
{
return v_b_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1___boxed(lean_object* v_as_804_, lean_object* v_i_805_, lean_object* v_stop_806_, lean_object* v_b_807_){
_start:
{
size_t v_i_boxed_808_; size_t v_stop_boxed_809_; lean_object* v_res_810_; 
v_i_boxed_808_ = lean_unbox_usize(v_i_805_);
lean_dec(v_i_805_);
v_stop_boxed_809_ = lean_unbox_usize(v_stop_806_);
lean_dec(v_stop_806_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_as_804_, v_i_boxed_808_, v_stop_boxed_809_, v_b_807_);
lean_dec_ref(v_as_804_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(size_t v_sz_811_, size_t v_i_812_, lean_object* v_bs_813_){
_start:
{
uint8_t v___x_814_; 
v___x_814_ = lean_usize_dec_lt(v_i_812_, v_sz_811_);
if (v___x_814_ == 0)
{
return v_bs_813_;
}
else
{
lean_object* v_v_815_; lean_object* v___x_816_; lean_object* v_bs_x27_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v_v_815_ = lean_array_uget(v_bs_813_, v_i_812_);
v___x_816_ = lean_unsigned_to_nat(0u);
v_bs_x27_817_ = lean_array_uset(v_bs_813_, v_i_812_, v___x_816_);
v_sz_818_ = lean_array_size(v_v_815_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_propagateArrayMetaData_spec__0(v_sz_818_, v___x_819_, v_v_815_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_812_, v___x_821_);
v___x_823_ = lean_array_uset(v_bs_x27_817_, v_i_812_, v___x_820_);
v_i_812_ = v___x_822_;
v_bs_813_ = v___x_823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_bs_827_){
_start:
{
size_t v_sz_boxed_828_; size_t v_i_boxed_829_; lean_object* v_res_830_; 
v_sz_boxed_828_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_829_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_boxed_828_, v_i_boxed_829_, v_bs_827_);
return v_res_830_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object* v_dss_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___y_838_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_836_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__1));
v___x_852_ = lean_array_get_size(v_dss_835_);
v___x_853_ = lean_nat_dec_lt(v___x_850_, v___x_852_);
if (v___x_853_ == 0)
{
v___y_838_ = v___x_851_;
goto v___jp_837_;
}
else
{
size_t v___x_854_; size_t v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((size_t)0ULL);
v___x_855_ = lean_usize_of_nat(v___x_852_);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__1(v_dss_835_, v___x_854_, v___x_855_, v___x_851_);
v___y_838_ = v___x_856_;
goto v___jp_837_;
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_839_ = lean_array_get_size(v___y_838_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_dec_eq(v___x_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; size_t v_sz_843_; size_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec_ref(v___y_838_);
v___x_842_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0, &l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries___closed__0);
v_sz_843_ = lean_array_size(v_dss_835_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries_spec__0(v_sz_843_, v___x_844_, v_dss_835_);
v___x_846_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v___x_842_, v___x_845_);
lean_dec_ref(v___x_845_);
v___x_847_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_846_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec_ref(v_dss_835_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get(v___x_836_, v___y_838_, v___x_848_);
lean_dec_ref(v___y_838_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(size_t v_sz_857_, size_t v_i_858_, lean_object* v_bs_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = lean_usize_dec_lt(v_i_858_, v_sz_857_);
if (v___x_860_ == 0)
{
return v_bs_859_;
}
else
{
lean_object* v_v_861_; lean_object* v_v_862_; uint8_t v_allowFill_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_877_; 
v_v_861_ = lean_array_uget(v_bs_859_, v_i_858_);
v_v_862_ = lean_ctor_get(v_v_861_, 0);
v_allowFill_863_ = lean_ctor_get_uint8(v_v_861_, sizeof(void*)*1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_v_861_);
if (v_isSharedCheck_877_ == 0)
{
v___x_865_ = v_v_861_;
v_isShared_866_ = v_isSharedCheck_877_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_v_862_);
lean_dec(v_v_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_877_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_doc_867_; lean_object* v___x_868_; lean_object* v_bs_x27_869_; lean_object* v___x_871_; 
v_doc_867_ = lean_ctor_get(v_v_862_, 0);
lean_inc(v_doc_867_);
lean_dec(v_v_862_);
v___x_868_ = lean_unsigned_to_nat(0u);
v_bs_x27_869_ = lean_array_uset(v_bs_859_, v_i_858_, v___x_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v_doc_867_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_doc_867_);
lean_ctor_set_uint8(v_reuseFailAlloc_876_, sizeof(void*)*1, v_allowFill_863_);
v___x_871_ = v_reuseFailAlloc_876_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; 
v___x_872_ = ((size_t)1ULL);
v___x_873_ = lean_usize_add(v_i_858_, v___x_872_);
v___x_874_ = lean_array_uset(v_bs_x27_869_, v_i_858_, v___x_871_);
v_i_858_ = v___x_873_;
v_bs_859_ = v___x_874_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0___boxed(lean_object* v_sz_878_, lean_object* v_i_879_, lean_object* v_bs_880_){
_start:
{
size_t v_sz_boxed_881_; size_t v_i_boxed_882_; lean_object* v_res_883_; 
v_sz_boxed_881_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_882_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_boxed_881_, v_i_boxed_882_, v_bs_880_);
return v_res_883_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_885_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsing(lean_object* v_sep_886_, lean_object* v_ds_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = lean_array_get_size(v_ds_887_);
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v_doc_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_doc_891_ = lean_ctor_get(v_sep_886_, 0);
lean_inc(v_doc_891_);
lean_dec_ref(v_sep_886_);
v_sz_892_ = lean_array_size(v_ds_887_);
v___x_893_ = ((size_t)0ULL);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_892_, v___x_893_, v_ds_887_);
v___x_895_ = l_Lean_Fmt_Doc_fillSomeUsing___redArg(v_doc_891_, v___x_894_);
v___x_896_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_895_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_v_900_; 
lean_dec_ref(v_sep_886_);
v___x_897_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_array_get(v___x_897_, v_ds_887_, v___x_898_);
lean_dec_ref(v_ds_887_);
v_v_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_v_900_);
lean_dec(v___x_899_);
return v_v_900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object* v_ds_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_array_get_size(v_ds_901_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_dec_eq(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
size_t v_sz_905_; size_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_sz_905_ = lean_array_size(v_ds_901_);
v___x_906_ = ((size_t)0ULL);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_905_, v___x_906_, v_ds_901_);
v___x_908_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v___x_907_);
v___x_909_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_908_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_v_913_; 
v___x_910_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_array_get(v___x_910_, v_ds_901_, v___x_911_);
lean_dec_ref(v_ds_901_);
v_v_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_v_913_);
lean_dec(v___x_912_);
return v_v_913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object* v_ds_914_, lean_object* v_wrap_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v___x_916_ = lean_array_get_size(v_ds_914_);
v___x_917_ = lean_unsigned_to_nat(1u);
v___x_918_ = lean_nat_dec_eq(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___f_919_; size_t v_sz_920_; size_t v___x_921_; lean_object* v_ds_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_919_, 0, v_wrap_915_);
v_sz_920_ = lean_array_size(v_ds_914_);
v___x_921_ = ((size_t)0ULL);
v_ds_922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_920_, v___x_921_, v_ds_914_);
v___x_923_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_922_, v___f_919_);
v___x_924_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_923_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_v_928_; 
lean_dec_ref(v_wrap_915_);
v___x_925_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_array_get(v___x_925_, v_ds_914_, v___x_926_);
lean_dec_ref(v_ds_914_);
v_v_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_v_928_);
lean_dec(v___x_927_);
return v_v_928_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object* v_d_929_){
_start:
{
lean_object* v_doc_930_; uint8_t v___x_931_; 
v_doc_930_ = lean_ctor_get(v_d_929_, 0);
v___x_931_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object* v_d_932_){
_start:
{
uint8_t v_res_933_; lean_object* v_r_934_; 
v_res_933_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_d_932_);
lean_dec_ref(v_d_932_);
v_r_934_ = lean_box(v_res_933_);
return v_r_934_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(lean_object* v_d_935_){
_start:
{
lean_object* v_doc_936_; uint8_t v___x_937_; 
v_doc_936_ = lean_ctor_get(v_d_935_, 0);
v___x_937_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_doc_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty___boxed(lean_object* v_d_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(v_d_938_);
lean_dec_ref(v_d_938_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isCompoundAtomic(lean_object* v_d_941_){
_start:
{
lean_object* v_doc_942_; uint8_t v___x_943_; 
v_doc_942_ = lean_ctor_get(v_d_941_, 0);
v___x_943_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_doc_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isCompoundAtomic___boxed(lean_object* v_d_944_){
_start:
{
uint8_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_d_944_);
lean_dec_ref(v_d_944_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object* v_d_947_){
_start:
{
lean_object* v_doc_948_; uint8_t v___x_949_; 
v_doc_948_ = lean_ctor_get(v_d_947_, 0);
v___x_949_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_doc_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAtomic___boxed(lean_object* v_d_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_d_950_);
lean_dec_ref(v_d_950_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instAppend___lam__0(lean_object* v_a_953_, lean_object* v_b_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_a_953_);
if (v___x_955_ == 0)
{
uint8_t v___x_956_; 
v___x_956_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_954_);
if (v___x_956_ == 0)
{
lean_object* v_doc_957_; lean_object* v_doc_958_; uint8_t v___x_959_; 
v_doc_957_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_doc_957_);
lean_dec_ref(v_a_953_);
v_doc_958_ = lean_ctor_get(v_b_954_, 0);
lean_inc(v_doc_958_);
lean_dec_ref(v_b_954_);
v___x_959_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_957_);
if (v___x_959_ == 0)
{
uint8_t v___x_960_; 
v___x_960_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_958_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_957_, v_doc_958_);
v___x_962_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_961_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; 
lean_dec(v_doc_958_);
v___x_963_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_957_);
return v___x_963_;
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v_doc_957_);
v___x_964_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_958_);
return v___x_964_;
}
}
else
{
lean_dec_ref(v_b_954_);
return v_a_953_;
}
}
else
{
lean_dec_ref(v_a_953_);
return v_b_954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(uint8_t v_x_967_){
_start:
{
switch(v_x_967_)
{
case 0:
{
lean_object* v___x_968_; 
v___x_968_ = lean_unsigned_to_nat(0u);
return v___x_968_;
}
case 1:
{
lean_object* v___x_969_; 
v___x_969_ = lean_unsigned_to_nat(1u);
return v___x_969_;
}
default: 
{
lean_object* v___x_970_; 
v___x_970_ = lean_unsigned_to_nat(2u);
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___boxed(lean_object* v_x_971_){
_start:
{
uint8_t v_x_boxed_972_; lean_object* v_res_973_; 
v_x_boxed_972_ = lean_unbox(v_x_971_);
v_res_973_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_x_boxed_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(lean_object* v_k_974_){
_start:
{
lean_inc(v_k_974_);
return v_k_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg___boxed(lean_object* v_k_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(v_k_975_);
lean_dec(v_k_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(lean_object* v_motive_977_, lean_object* v_ctorIdx_978_, uint8_t v_t_979_, lean_object* v_h_980_, lean_object* v_k_981_){
_start:
{
lean_inc(v_k_981_);
return v_k_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___boxed(lean_object* v_motive_982_, lean_object* v_ctorIdx_983_, lean_object* v_t_984_, lean_object* v_h_985_, lean_object* v_k_986_){
_start:
{
uint8_t v_t_boxed_987_; lean_object* v_res_988_; 
v_t_boxed_987_ = lean_unbox(v_t_984_);
v_res_988_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(v_motive_982_, v_ctorIdx_983_, v_t_boxed_987_, v_h_985_, v_k_986_);
lean_dec(v_k_986_);
lean_dec(v_ctorIdx_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(lean_object* v_coequal_989_){
_start:
{
lean_inc(v_coequal_989_);
return v_coequal_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg___boxed(lean_object* v_coequal_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(v_coequal_990_);
lean_dec(v_coequal_990_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(lean_object* v_motive_992_, uint8_t v_t_993_, lean_object* v_h_994_, lean_object* v_coequal_995_){
_start:
{
lean_inc(v_coequal_995_);
return v_coequal_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___boxed(lean_object* v_motive_996_, lean_object* v_t_997_, lean_object* v_h_998_, lean_object* v_coequal_999_){
_start:
{
uint8_t v_t_boxed_1000_; lean_object* v_res_1001_; 
v_t_boxed_1000_ = lean_unbox(v_t_997_);
v_res_1001_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(v_motive_996_, v_t_boxed_1000_, v_h_998_, v_coequal_999_);
lean_dec(v_coequal_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(lean_object* v_preferSticky_1002_){
_start:
{
lean_inc(v_preferSticky_1002_);
return v_preferSticky_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg___boxed(lean_object* v_preferSticky_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(v_preferSticky_1003_);
lean_dec(v_preferSticky_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(lean_object* v_motive_1005_, uint8_t v_t_1006_, lean_object* v_h_1007_, lean_object* v_preferSticky_1008_){
_start:
{
lean_inc(v_preferSticky_1008_);
return v_preferSticky_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___boxed(lean_object* v_motive_1009_, lean_object* v_t_1010_, lean_object* v_h_1011_, lean_object* v_preferSticky_1012_){
_start:
{
uint8_t v_t_boxed_1013_; lean_object* v_res_1014_; 
v_t_boxed_1013_ = lean_unbox(v_t_1010_);
v_res_1014_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(v_motive_1009_, v_t_boxed_1013_, v_h_1011_, v_preferSticky_1012_);
lean_dec(v_preferSticky_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(lean_object* v_preferUnsticky_1015_){
_start:
{
lean_inc(v_preferUnsticky_1015_);
return v_preferUnsticky_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg___boxed(lean_object* v_preferUnsticky_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(v_preferUnsticky_1016_);
lean_dec(v_preferUnsticky_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(lean_object* v_motive_1018_, uint8_t v_t_1019_, lean_object* v_h_1020_, lean_object* v_preferUnsticky_1021_){
_start:
{
lean_inc(v_preferUnsticky_1021_);
return v_preferUnsticky_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___boxed(lean_object* v_motive_1022_, lean_object* v_t_1023_, lean_object* v_h_1024_, lean_object* v_preferUnsticky_1025_){
_start:
{
uint8_t v_t_boxed_1026_; lean_object* v_res_1027_; 
v_t_boxed_1026_ = lean_unbox(v_t_1023_);
v_res_1027_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(v_motive_1022_, v_t_boxed_1026_, v_h_1024_, v_preferUnsticky_1025_);
lean_dec(v_preferUnsticky_1025_);
return v_res_1027_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default(void){
_start:
{
uint8_t v___x_1028_; 
v___x_1028_ = 0;
return v___x_1028_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind(void){
_start:
{
uint8_t v___x_1029_; 
v___x_1029_ = 0;
return v___x_1029_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t v_x_1030_, uint8_t v_y_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1032_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_x_1030_);
v___x_1033_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_y_1031_);
v___x_1034_ = lean_nat_dec_eq(v___x_1032_, v___x_1033_);
lean_dec(v___x_1033_);
lean_dec(v___x_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed(lean_object* v_x_1035_, lean_object* v_y_1036_){
_start:
{
uint8_t v_x_21__boxed_1037_; uint8_t v_y_22__boxed_1038_; uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_x_21__boxed_1037_ = lean_unbox(v_x_1035_);
v_y_22__boxed_1038_ = lean_unbox(v_y_1036_);
v_res_1039_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_x_21__boxed_1037_, v_y_22__boxed_1038_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0(void){
_start:
{
uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = 0;
v___x_1044_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*1, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default(void){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0, &l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky(void){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___lam__0(lean_object* v_v_1059_, lean_object* v_f_1060_){
_start:
{
lean_object* v_stickyVariant_1061_; uint8_t v_kind_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
v_stickyVariant_1061_ = lean_ctor_get(v_v_1059_, 0);
v_kind_1062_ = lean_ctor_get_uint8(v_v_1059_, sizeof(void*)*1);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_v_1059_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1064_ = v_v_1059_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_stickyVariant_1061_);
lean_dec(v_v_1059_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_stickyVariant_1061_, v_f_1060_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
lean_ctor_set_uint8(v_reuseFailAlloc_1069_, sizeof(void*)*1, v_kind_1062_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object* v_nonStickyVariant_1072_, lean_object* v_stickyVariant_1073_, uint8_t v_kind_1074_){
_start:
{
lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___f_1075_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_sticky___closed__0));
v___x_1076_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1077_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1078_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1078_, 0, v_stickyVariant_1073_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*1, v_kind_1074_);
v___x_1079_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1076_, v___x_1077_, v_nonStickyVariant_1072_, v___x_1078_, v___f_1075_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___boxed(lean_object* v_nonStickyVariant_1080_, lean_object* v_stickyVariant_1081_, lean_object* v_kind_1082_){
_start:
{
uint8_t v_kind_boxed_1083_; lean_object* v_res_1084_; 
v_kind_boxed_1083_ = lean_unbox(v_kind_1082_);
v_res_1084_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_1080_, v_stickyVariant_1081_, v_kind_boxed_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object* v_doc_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1087_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1086_, v_doc_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object* v_doc_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_doc_1088_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
else
{
lean_object* v_val_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1100_; 
v_val_1091_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1093_ = v___x_1089_;
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_val_1091_);
lean_dec(v___x_1089_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint8_t v_kind_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v_kind_1095_ = lean_ctor_get_uint8(v_val_1091_, sizeof(void*)*1);
lean_dec(v_val_1091_);
v___x_1096_ = lean_box(v_kind_1095_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object* v_inner_1101_, lean_object* v_f_1102_, lean_object* v_kind_x3f_1103_){
_start:
{
lean_object* v_nonStickyOuter_1104_; lean_object* v___x_1105_; 
lean_inc_ref(v_f_1102_);
lean_inc_ref(v_inner_1101_);
v_nonStickyOuter_1104_ = lean_apply_1(v_f_1102_, v_inner_1101_);
v___x_1105_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_inner_1101_);
if (lean_obj_tag(v___x_1105_) == 1)
{
lean_object* v_val_1106_; lean_object* v_stickyVariant_1107_; uint8_t v_kind_1108_; lean_object* v_stickyOuter_1109_; 
v_val_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_val_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_stickyVariant_1107_ = lean_ctor_get(v_val_1106_, 0);
lean_inc_ref(v_stickyVariant_1107_);
v_kind_1108_ = lean_ctor_get_uint8(v_val_1106_, sizeof(void*)*1);
lean_dec(v_val_1106_);
v_stickyOuter_1109_ = lean_apply_1(v_f_1102_, v_stickyVariant_1107_);
if (lean_obj_tag(v_kind_x3f_1103_) == 0)
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1104_, v_stickyOuter_1109_, v_kind_1108_);
return v___x_1110_;
}
else
{
lean_object* v_val_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; 
v_val_1111_ = lean_ctor_get(v_kind_x3f_1103_, 0);
v___x_1112_ = lean_unbox(v_val_1111_);
v___x_1113_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1104_, v_stickyOuter_1109_, v___x_1112_);
return v___x_1113_;
}
}
else
{
lean_dec(v___x_1105_);
lean_dec_ref(v_f_1102_);
return v_nonStickyOuter_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness___boxed(lean_object* v_inner_1114_, lean_object* v_f_1115_, lean_object* v_kind_x3f_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_inner_1114_, v_f_1115_, v_kind_x3f_1116_);
lean_dec(v_kind_x3f_1116_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx(lean_object* v_x_1118_){
_start:
{
switch(lean_obj_tag(v_x_1118_))
{
case 0:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
return v___x_1119_;
}
case 1:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_unsigned_to_nat(1u);
return v___x_1120_;
}
default: 
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_unsigned_to_nat(2u);
return v___x_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___boxed(lean_object* v_x_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx(v_x_1122_);
lean_dec(v_x_1122_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(lean_object* v_t_1124_, lean_object* v_k_1125_){
_start:
{
if (lean_obj_tag(v_t_1124_) == 2)
{
uint8_t v_allowFlattening_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_allowFlattening_1126_ = lean_ctor_get_uint8(v_t_1124_, 0);
v___x_1127_ = lean_box(v_allowFlattening_1126_);
v___x_1128_ = lean_apply_1(v_k_1125_, v___x_1127_);
return v___x_1128_;
}
else
{
return v_k_1125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg___boxed(lean_object* v_t_1129_, lean_object* v_k_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1129_, v_k_1130_);
lean_dec(v_t_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(lean_object* v_motive_1132_, lean_object* v_ctorIdx_1133_, lean_object* v_t_1134_, lean_object* v_h_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1134_, v_k_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___boxed(lean_object* v_motive_1138_, lean_object* v_ctorIdx_1139_, lean_object* v_t_1140_, lean_object* v_h_1141_, lean_object* v_k_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(v_motive_1138_, v_ctorIdx_1139_, v_t_1140_, v_h_1141_, v_k_1142_);
lean_dec(v_t_1140_);
lean_dec(v_ctorIdx_1139_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(lean_object* v_t_1144_, lean_object* v_coequal_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1144_, v_coequal_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg___boxed(lean_object* v_t_1147_, lean_object* v_coequal_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(v_t_1147_, v_coequal_1148_);
lean_dec(v_t_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(lean_object* v_motive_1150_, lean_object* v_t_1151_, lean_object* v_h_1152_, lean_object* v_coequal_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1151_, v_coequal_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___boxed(lean_object* v_motive_1155_, lean_object* v_t_1156_, lean_object* v_h_1157_, lean_object* v_coequal_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(v_motive_1155_, v_t_1156_, v_h_1157_, v_coequal_1158_);
lean_dec(v_t_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(lean_object* v_t_1160_, lean_object* v_preferUnsticky_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1160_, v_preferUnsticky_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg___boxed(lean_object* v_t_1163_, lean_object* v_preferUnsticky_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(v_t_1163_, v_preferUnsticky_1164_);
lean_dec(v_t_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(lean_object* v_motive_1166_, lean_object* v_t_1167_, lean_object* v_h_1168_, lean_object* v_preferUnsticky_1169_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1167_, v_preferUnsticky_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___boxed(lean_object* v_motive_1171_, lean_object* v_t_1172_, lean_object* v_h_1173_, lean_object* v_preferUnsticky_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(v_motive_1171_, v_t_1172_, v_h_1173_, v_preferUnsticky_1174_);
lean_dec(v_t_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(lean_object* v_t_1176_, lean_object* v_preferSticky_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1176_, v_preferSticky_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg___boxed(lean_object* v_t_1179_, lean_object* v_preferSticky_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(v_t_1179_, v_preferSticky_1180_);
lean_dec(v_t_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(lean_object* v_motive_1182_, lean_object* v_t_1183_, lean_object* v_h_1184_, lean_object* v_preferSticky_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1183_, v_preferSticky_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___boxed(lean_object* v_motive_1187_, lean_object* v_t_1188_, lean_object* v_h_1189_, lean_object* v_preferSticky_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(v_motive_1187_, v_t_1188_, v_h_1189_, v_preferSticky_1190_);
lean_dec(v_t_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object* v_s_1192_, uint8_t v_allowFlattening_1193_){
_start:
{
uint8_t v_kind_1194_; 
v_kind_1194_ = lean_ctor_get_uint8(v_s_1192_, sizeof(void*)*1);
switch(v_kind_1194_)
{
case 0:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_box(0);
return v___x_1195_;
}
case 1:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1196_, 0, v_allowFlattening_1193_);
return v___x_1196_;
}
default: 
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_box(1);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky___boxed(lean_object* v_s_1198_, lean_object* v_allowFlattening_1199_){
_start:
{
uint8_t v_allowFlattening_boxed_1200_; lean_object* v_res_1201_; 
v_allowFlattening_boxed_1200_ = lean_unbox(v_allowFlattening_1199_);
v_res_1201_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_s_1198_, v_allowFlattening_boxed_1200_);
lean_dec_ref(v_s_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object* v_doc_1202_, lean_object* v_stickyDoc_1203_, lean_object* v_cfg_1204_){
_start:
{
switch(lean_obj_tag(v_cfg_1204_))
{
case 0:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1205_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1203_);
v___x_1206_ = lean_unsigned_to_nat(2u);
v___x_1207_ = lean_mk_empty_array_with_capacity(v___x_1206_);
v___x_1208_ = lean_array_push(v___x_1207_, v___x_1205_);
v___x_1209_ = lean_array_push(v___x_1208_, v_doc_1202_);
v___x_1210_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1209_);
return v___x_1210_;
}
case 1:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1211_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1203_);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v___x_1211_, v___x_1212_);
v___x_1214_ = lean_unsigned_to_nat(2u);
v___x_1215_ = lean_mk_empty_array_with_capacity(v___x_1214_);
v___x_1216_ = lean_array_push(v___x_1215_, v_doc_1202_);
v___x_1217_ = lean_array_push(v___x_1216_, v___x_1213_);
v___x_1218_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1217_);
return v___x_1218_;
}
default: 
{
uint8_t v_allowFlattening_1219_; 
v_allowFlattening_1219_ = lean_ctor_get_uint8(v_cfg_1204_, 0);
if (v_allowFlattening_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1220_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1203_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1202_, v___x_1221_);
v___x_1223_ = lean_unsigned_to_nat(2u);
v___x_1224_ = lean_mk_empty_array_with_capacity(v___x_1223_);
v___x_1225_ = lean_array_push(v___x_1224_, v___x_1220_);
v___x_1226_ = lean_array_push(v___x_1225_, v___x_1222_);
v___x_1227_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1228_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1203_);
lean_inc_ref(v_doc_1202_);
v___x_1229_ = l_Lean_Fmt_TaggedDoc_flattened(v_doc_1202_);
v___x_1230_ = lean_unsigned_to_nat(1u);
v___x_1231_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1202_, v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(3u);
v___x_1233_ = lean_mk_empty_array_with_capacity(v___x_1232_);
v___x_1234_ = lean_array_push(v___x_1233_, v___x_1228_);
v___x_1235_ = lean_array_push(v___x_1234_, v___x_1229_);
v___x_1236_ = lean_array_push(v___x_1235_, v___x_1231_);
v___x_1237_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1236_);
return v___x_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt___boxed(lean_object* v_doc_1238_, lean_object* v_stickyDoc_1239_, lean_object* v_cfg_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1238_, v_stickyDoc_1239_, v_cfg_1240_);
lean_dec(v_cfg_1240_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0(lean_object* v_s_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0));
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v_s_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0(lean_object* v_doc_x3f_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_doc_x3f_1248_);
lean_ctor_set(v___x_1250_, 2, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object* v_doc_x3f_1253_, lean_object* v_sepBefore_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_sepBefore_1254_);
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1255_);
lean_ctor_set(v___x_1257_, 1, v_doc_x3f_1253_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object* v_doc_x3f_1258_, lean_object* v_sepAfter_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_sepAfter_1259_);
v___x_1262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1260_);
lean_ctor_set(v___x_1262_, 1, v_doc_x3f_1258_);
lean_ctor_set(v___x_1262_, 2, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(lean_object* v_as_1263_, size_t v_i_1264_, size_t v_stop_1265_, lean_object* v_b_1266_){
_start:
{
lean_object* v___y_1268_; uint8_t v___x_1272_; 
v___x_1272_ = lean_usize_dec_eq(v_i_1264_, v_stop_1265_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v_doc_x3f_1274_; 
v___x_1273_ = lean_array_uget_borrowed(v_as_1263_, v_i_1264_);
v_doc_x3f_1274_ = lean_ctor_get(v___x_1273_, 1);
if (lean_obj_tag(v_doc_x3f_1274_) == 0)
{
v___y_1268_ = v_b_1266_;
goto v___jp_1267_;
}
else
{
lean_object* v_sepBefore_x3f_1275_; lean_object* v_sepAfter_x3f_1276_; lean_object* v_val_1277_; uint8_t v___x_1278_; 
v_sepBefore_x3f_1275_ = lean_ctor_get(v___x_1273_, 0);
v_sepAfter_x3f_1276_ = lean_ctor_get(v___x_1273_, 2);
v_val_1277_ = lean_ctor_get(v_doc_x3f_1274_, 0);
v___x_1278_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_inc(v_sepAfter_x3f_1276_);
lean_inc(v_val_1277_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_val_1277_);
lean_ctor_set(v___x_1279_, 1, v_sepAfter_x3f_1276_);
lean_inc(v_sepBefore_x3f_1275_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_sepBefore_x3f_1275_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_array_push(v_b_1266_, v___x_1280_);
v___y_1268_ = v___x_1281_;
goto v___jp_1267_;
}
else
{
v___y_1268_ = v_b_1266_;
goto v___jp_1267_;
}
}
}
else
{
return v_b_1266_;
}
v___jp_1267_:
{
size_t v___x_1269_; size_t v___x_1270_; 
v___x_1269_ = ((size_t)1ULL);
v___x_1270_ = lean_usize_add(v_i_1264_, v___x_1269_);
v_i_1264_ = v___x_1270_;
v_b_1266_ = v___y_1268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0___boxed(lean_object* v_as_1282_, lean_object* v_i_1283_, lean_object* v_stop_1284_, lean_object* v_b_1285_){
_start:
{
size_t v_i_boxed_1286_; size_t v_stop_boxed_1287_; lean_object* v_res_1288_; 
v_i_boxed_1286_ = lean_unbox_usize(v_i_1283_);
lean_dec(v_i_1283_);
v_stop_boxed_1287_ = lean_unbox_usize(v_stop_1284_);
lean_dec(v_stop_1284_);
v_res_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1282_, v_i_boxed_1286_, v_stop_boxed_1287_, v_b_1285_);
lean_dec_ref(v_as_1282_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(lean_object* v_as_1291_, lean_object* v_start_1292_, lean_object* v_stop_1293_){
_start:
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0));
v___x_1295_ = lean_nat_dec_lt(v_start_1292_, v_stop_1293_);
if (v___x_1295_ == 0)
{
return v___x_1294_;
}
else
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = lean_array_get_size(v_as_1291_);
v___x_1297_ = lean_nat_dec_le(v_stop_1293_, v___x_1296_);
if (v___x_1297_ == 0)
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_nat_dec_lt(v_start_1292_, v___x_1296_);
if (v___x_1298_ == 0)
{
return v___x_1294_;
}
else
{
size_t v___x_1299_; size_t v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_usize_of_nat(v_start_1292_);
v___x_1300_ = lean_usize_of_nat(v___x_1296_);
v___x_1301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1291_, v___x_1299_, v___x_1300_, v___x_1294_);
return v___x_1301_;
}
}
else
{
size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = lean_usize_of_nat(v_start_1292_);
v___x_1303_ = lean_usize_of_nat(v_stop_1293_);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1291_, v___x_1302_, v___x_1303_, v___x_1294_);
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___boxed(lean_object* v_as_1305_, lean_object* v_start_1306_, lean_object* v_stop_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_as_1305_, v_start_1306_, v_stop_1307_);
lean_dec(v_stop_1307_);
lean_dec(v_start_1306_);
lean_dec_ref(v_as_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(lean_object* v_cs_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_array_get_size(v_cs_1309_);
v___x_1312_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_cs_1309_, v___x_1310_, v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs___boxed(lean_object* v_cs_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1313_);
lean_dec_ref(v_cs_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_bs_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1316_, v_sz_1315_);
if (v___x_1318_ == 0)
{
return v_bs_1317_;
}
else
{
lean_object* v_v_1319_; lean_object* v_snd_1320_; lean_object* v_fst_1321_; lean_object* v_fst_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1335_; 
v_v_1319_ = lean_array_uget_borrowed(v_bs_1317_, v_i_1316_);
v_snd_1320_ = lean_ctor_get(v_v_1319_, 1);
lean_inc(v_snd_1320_);
v_fst_1321_ = lean_ctor_get(v_v_1319_, 0);
lean_inc(v_fst_1321_);
v_fst_1322_ = lean_ctor_get(v_snd_1320_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_snd_1320_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_snd_1320_, 1);
lean_dec(v_unused_1336_);
v___x_1324_ = v_snd_1320_;
v_isShared_1325_ = v_isSharedCheck_1335_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_fst_1322_);
lean_dec(v_snd_1320_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1335_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v_bs_x27_1327_; lean_object* v___x_1329_; 
v___x_1326_ = lean_unsigned_to_nat(0u);
v_bs_x27_1327_ = lean_array_uset(v_bs_1317_, v_i_1316_, v___x_1326_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v_fst_1322_);
lean_ctor_set(v___x_1324_, 0, v_fst_1321_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_fst_1321_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_fst_1322_);
v___x_1329_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
size_t v___x_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = ((size_t)1ULL);
v___x_1331_ = lean_usize_add(v_i_1316_, v___x_1330_);
v___x_1332_ = lean_array_uset(v_bs_x27_1327_, v_i_1316_, v___x_1329_);
v_i_1316_ = v___x_1331_;
v_bs_1317_ = v___x_1332_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0___boxed(lean_object* v_sz_1337_, lean_object* v_i_1338_, lean_object* v_bs_1339_){
_start:
{
size_t v_sz_boxed_1340_; size_t v_i_boxed_1341_; lean_object* v_res_1342_; 
v_sz_boxed_1340_ = lean_unbox_usize(v_sz_1337_);
lean_dec(v_sz_1337_);
v_i_boxed_1341_ = lean_unbox_usize(v_i_1338_);
lean_dec(v_i_1338_);
v_res_1342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_boxed_1340_, v_i_boxed_1341_, v_bs_1339_);
return v_res_1342_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v___x_1343_);
return v___x_1345_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v___x_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(lean_object* v_upperBound_1349_, lean_object* v_a_1350_, lean_object* v_b_1351_){
_start:
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_nat_dec_lt(v_a_1350_, v_upperBound_1349_);
if (v___x_1352_ == 0)
{
lean_dec(v_a_1350_);
return v_b_1351_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_snd_1355_; lean_object* v_snd_1356_; lean_object* v___x_1357_; lean_object* v_a_1359_; 
v___x_1353_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1354_ = lean_array_get_borrowed(v___x_1353_, v_b_1351_, v_a_1350_);
v_snd_1355_ = lean_ctor_get(v___x_1354_, 1);
v_snd_1356_ = lean_ctor_get(v_snd_1355_, 1);
v___x_1357_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1356_) == 1)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1362_ = lean_nat_add(v_a_1350_, v___x_1357_);
v___x_1363_ = lean_array_get_size(v_b_1351_);
v___x_1364_ = lean_nat_dec_lt(v___x_1362_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_dec(v___x_1362_);
v_a_1359_ = v_b_1351_;
goto v___jp_1358_;
}
else
{
lean_object* v_v_1365_; lean_object* v_snd_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1376_; 
lean_inc_ref(v_snd_1356_);
v_v_1365_ = lean_array_fget(v_b_1351_, v___x_1362_);
v_snd_1366_ = lean_ctor_get(v_v_1365_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_v_1365_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v_v_1365_, 0);
lean_dec(v_unused_1377_);
v___x_1368_ = v_v_1365_;
v_isShared_1369_ = v_isSharedCheck_1376_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snd_1366_);
lean_dec(v_v_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1376_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v_xs_x27_1371_; lean_object* v___x_1373_; 
v___x_1370_ = lean_box(0);
v_xs_x27_1371_ = lean_array_fset(v_b_1351_, v___x_1362_, v___x_1370_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_snd_1356_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_snd_1356_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_snd_1366_);
v___x_1373_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_array_fset(v_xs_x27_1371_, v___x_1362_, v___x_1373_);
lean_dec(v___x_1362_);
v_a_1359_ = v___x_1374_;
goto v___jp_1358_;
}
}
}
}
else
{
v_a_1359_ = v_b_1351_;
goto v___jp_1358_;
}
v___jp_1358_:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_nat_add(v_a_1350_, v___x_1357_);
lean_dec(v_a_1350_);
v_a_1350_ = v___x_1360_;
v_b_1351_ = v_a_1359_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___boxed(lean_object* v_upperBound_1378_, lean_object* v_a_1379_, lean_object* v_b_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1378_, v_a_1379_, v_b_1380_);
lean_dec(v_upperBound_1378_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(lean_object* v_upperBound_1382_, lean_object* v_a_1383_, lean_object* v_b_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_nat_dec_lt(v_a_1383_, v_upperBound_1382_);
if (v___x_1385_ == 0)
{
lean_dec(v_a_1383_);
return v_b_1384_;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_snd_1389_; lean_object* v_snd_1390_; lean_object* v___x_1391_; lean_object* v_a_1393_; 
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1388_ = lean_array_get_borrowed(v___x_1387_, v_b_1384_, v_a_1383_);
v_snd_1389_ = lean_ctor_get(v___x_1388_, 1);
v_snd_1390_ = lean_ctor_get(v_snd_1389_, 1);
v___x_1391_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1390_) == 1)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_fst_1398_; 
v___x_1396_ = lean_nat_add(v_a_1383_, v___x_1391_);
v___x_1397_ = lean_array_get_borrowed(v___x_1387_, v_b_1384_, v___x_1396_);
lean_dec(v___x_1396_);
v_fst_1398_ = lean_ctor_get(v___x_1397_, 0);
if (lean_obj_tag(v_fst_1398_) == 1)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = lean_array_get_size(v_b_1384_);
v___x_1400_ = lean_nat_dec_lt(v_a_1383_, v___x_1399_);
if (v___x_1400_ == 0)
{
v_a_1393_ = v_b_1384_;
goto v___jp_1392_;
}
else
{
lean_object* v_v_1401_; lean_object* v_snd_1402_; lean_object* v_fst_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1422_; 
v_v_1401_ = lean_array_fget(v_b_1384_, v_a_1383_);
v_snd_1402_ = lean_ctor_get(v_v_1401_, 1);
v_fst_1403_ = lean_ctor_get(v_v_1401_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_v_1401_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1405_ = v_v_1401_;
v_isShared_1406_ = v_isSharedCheck_1422_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1403_);
lean_dec(v_v_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1422_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v_fst_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1420_; 
v_fst_1407_ = lean_ctor_get(v_snd_1402_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_snd_1402_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v_snd_1402_, 1);
lean_dec(v_unused_1421_);
v___x_1409_ = v_snd_1402_;
v_isShared_1410_ = v_isSharedCheck_1420_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_fst_1407_);
lean_dec(v_snd_1402_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1420_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v_xs_x27_1412_; lean_object* v___x_1414_; 
v___x_1411_ = lean_box(0);
v_xs_x27_1412_ = lean_array_fset(v_b_1384_, v_a_1383_, v___x_1411_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 1, v___x_1386_);
v___x_1414_ = v___x_1409_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_fst_1407_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1386_);
v___x_1414_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 1, v___x_1414_);
v___x_1416_ = v___x_1405_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_fst_1403_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; 
v___x_1417_ = lean_array_fset(v_xs_x27_1412_, v_a_1383_, v___x_1416_);
v_a_1393_ = v___x_1417_;
goto v___jp_1392_;
}
}
}
}
}
}
else
{
v_a_1393_ = v_b_1384_;
goto v___jp_1392_;
}
}
else
{
v_a_1393_ = v_b_1384_;
goto v___jp_1392_;
}
v___jp_1392_:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_nat_add(v_a_1383_, v___x_1391_);
lean_dec(v_a_1383_);
v_a_1383_ = v___x_1394_;
v_b_1384_ = v_a_1393_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg___boxed(lean_object* v_upperBound_1423_, lean_object* v_a_1424_, lean_object* v_b_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1423_, v_a_1424_, v_b_1425_);
lean_dec(v_upperBound_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(lean_object* v_upperBound_1427_, lean_object* v_a_1428_, lean_object* v_b_1429_){
_start:
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_nat_dec_lt(v_a_1428_, v_upperBound_1427_);
if (v___x_1430_ == 0)
{
return v_b_1429_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v_snd_1434_; lean_object* v_snd_1435_; lean_object* v___x_1436_; lean_object* v_a_1438_; 
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1433_ = lean_array_get_borrowed(v___x_1432_, v_b_1429_, v_a_1428_);
v_snd_1434_ = lean_ctor_get(v___x_1433_, 1);
v_snd_1435_ = lean_ctor_get(v_snd_1434_, 1);
v___x_1436_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1435_) == 1)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_fst_1443_; 
v___x_1441_ = lean_nat_add(v_a_1428_, v___x_1436_);
v___x_1442_ = lean_array_get_borrowed(v___x_1432_, v_b_1429_, v___x_1441_);
lean_dec(v___x_1441_);
v_fst_1443_ = lean_ctor_get(v___x_1442_, 0);
if (lean_obj_tag(v_fst_1443_) == 1)
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_array_get_size(v_b_1429_);
v___x_1445_ = lean_nat_dec_lt(v_a_1428_, v___x_1444_);
if (v___x_1445_ == 0)
{
v_a_1438_ = v_b_1429_;
goto v___jp_1437_;
}
else
{
lean_object* v_v_1446_; lean_object* v_snd_1447_; lean_object* v_fst_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1467_; 
v_v_1446_ = lean_array_fget(v_b_1429_, v_a_1428_);
v_snd_1447_ = lean_ctor_get(v_v_1446_, 1);
v_fst_1448_ = lean_ctor_get(v_v_1446_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_v_1446_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1450_ = v_v_1446_;
v_isShared_1451_ = v_isSharedCheck_1467_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_snd_1447_);
lean_inc(v_fst_1448_);
lean_dec(v_v_1446_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1467_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_fst_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1465_; 
v_fst_1452_ = lean_ctor_get(v_snd_1447_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_snd_1447_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_snd_1447_, 1);
lean_dec(v_unused_1466_);
v___x_1454_ = v_snd_1447_;
v_isShared_1455_ = v_isSharedCheck_1465_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_fst_1452_);
lean_dec(v_snd_1447_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1465_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v_xs_x27_1457_; lean_object* v___x_1459_; 
v___x_1456_ = lean_box(0);
v_xs_x27_1457_ = lean_array_fset(v_b_1429_, v_a_1428_, v___x_1456_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v___x_1431_);
v___x_1459_ = v___x_1454_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_fst_1452_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v___x_1431_);
v___x_1459_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1461_; 
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 1, v___x_1459_);
v___x_1461_ = v___x_1450_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_fst_1448_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_array_fset(v_xs_x27_1457_, v_a_1428_, v___x_1461_);
v_a_1438_ = v___x_1462_;
goto v___jp_1437_;
}
}
}
}
}
}
else
{
v_a_1438_ = v_b_1429_;
goto v___jp_1437_;
}
}
else
{
v_a_1438_ = v_b_1429_;
goto v___jp_1437_;
}
v___jp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_nat_add(v_a_1428_, v___x_1436_);
v___x_1440_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1427_, v___x_1439_, v_a_1438_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg___boxed(lean_object* v_upperBound_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1468_, v_a_1469_, v_b_1470_);
lean_dec(v_a_1469_);
lean_dec(v_upperBound_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(lean_object* v_entries_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1487_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1473_ = lean_unsigned_to_nat(0u);
v___x_1515_ = lean_array_get_size(v_entries_1472_);
v___x_1516_ = lean_nat_dec_lt(v___x_1473_, v___x_1515_);
if (v___x_1516_ == 0)
{
v___y_1487_ = v_entries_1472_;
goto v___jp_1486_;
}
else
{
lean_object* v_v_1517_; lean_object* v_snd_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1529_; 
v_v_1517_ = lean_array_fget(v_entries_1472_, v___x_1473_);
v_snd_1518_ = lean_ctor_get(v_v_1517_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_v_1517_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_v_1517_, 0);
lean_dec(v_unused_1530_);
v___x_1520_ = v_v_1517_;
v_isShared_1521_ = v_isSharedCheck_1529_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_snd_1518_);
lean_dec(v_v_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1529_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v_xs_x27_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1522_ = lean_box(0);
v_xs_x27_1523_ = lean_array_fset(v_entries_1472_, v___x_1473_, v___x_1522_);
v___x_1524_ = lean_box(0);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1524_);
v___x_1526_ = v___x_1520_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_snd_1518_);
v___x_1526_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_array_fset(v_xs_x27_1523_, v___x_1473_, v___x_1526_);
v___y_1487_ = v___x_1527_;
goto v___jp_1486_;
}
}
}
v___jp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; size_t v_sz_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1477_ = lean_array_get_size(v___y_1476_);
v___x_1478_ = lean_nat_sub(v___x_1477_, v___y_1475_);
v___x_1479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v___x_1478_, v___x_1473_, v___y_1476_);
lean_dec(v___x_1478_);
v___x_1480_ = lean_array_get_size(v___x_1479_);
v___x_1481_ = lean_nat_sub(v___x_1480_, v___y_1475_);
v___x_1482_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v___x_1481_, v___x_1473_, v___x_1479_);
lean_dec(v___x_1481_);
v_sz_1483_ = lean_array_size(v___x_1482_);
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_1483_, v___x_1484_, v___x_1482_);
return v___x_1485_;
}
v___jp_1486_:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1488_ = lean_array_get_size(v___y_1487_);
v___x_1489_ = lean_unsigned_to_nat(1u);
v___x_1490_ = lean_nat_sub(v___x_1488_, v___x_1489_);
v___x_1491_ = lean_nat_dec_lt(v___x_1490_, v___x_1488_);
if (v___x_1491_ == 0)
{
lean_dec(v___x_1490_);
v___y_1475_ = v___x_1489_;
v___y_1476_ = v___y_1487_;
goto v___jp_1474_;
}
else
{
lean_object* v_v_1492_; lean_object* v_snd_1493_; lean_object* v_fst_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1514_; 
v_v_1492_ = lean_array_fget(v___y_1487_, v___x_1490_);
v_snd_1493_ = lean_ctor_get(v_v_1492_, 1);
v_fst_1494_ = lean_ctor_get(v_v_1492_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_v_1492_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1496_ = v_v_1492_;
v_isShared_1497_ = v_isSharedCheck_1514_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1493_);
lean_inc(v_fst_1494_);
lean_dec(v_v_1492_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1514_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_fst_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1512_; 
v_fst_1498_ = lean_ctor_get(v_snd_1493_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_snd_1493_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_snd_1493_, 1);
lean_dec(v_unused_1513_);
v___x_1500_ = v_snd_1493_;
v_isShared_1501_ = v_isSharedCheck_1512_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_fst_1498_);
lean_dec(v_snd_1493_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1512_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v_xs_x27_1503_; lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1502_ = lean_box(0);
v_xs_x27_1503_ = lean_array_fset(v___y_1487_, v___x_1490_, v___x_1502_);
v___x_1504_ = lean_box(0);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1504_);
v___x_1506_ = v___x_1500_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_fst_1498_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v___x_1506_);
v___x_1508_ = v___x_1496_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_fst_1494_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_array_fset(v_xs_x27_1503_, v___x_1490_, v___x_1508_);
lean_dec(v___x_1490_);
v___y_1475_ = v___x_1489_;
v___y_1476_ = v___x_1509_;
goto v___jp_1474_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(lean_object* v_upperBound_1531_, lean_object* v_inst_1532_, lean_object* v_R_1533_, lean_object* v_a_1534_, lean_object* v_b_1535_, lean_object* v_c_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1531_, v_a_1534_, v_b_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___boxed(lean_object* v_upperBound_1538_, lean_object* v_inst_1539_, lean_object* v_R_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_, lean_object* v_c_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(v_upperBound_1538_, v_inst_1539_, v_R_1540_, v_a_1541_, v_b_1542_, v_c_1543_);
lean_dec(v_upperBound_1538_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(lean_object* v_upperBound_1545_, lean_object* v_inst_1546_, lean_object* v_R_1547_, lean_object* v_a_1548_, lean_object* v_b_1549_, lean_object* v_c_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1545_, v_a_1548_, v_b_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___boxed(lean_object* v_upperBound_1552_, lean_object* v_inst_1553_, lean_object* v_R_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_, lean_object* v_c_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(v_upperBound_1552_, v_inst_1553_, v_R_1554_, v_a_1555_, v_b_1556_, v_c_1557_);
lean_dec(v_a_1555_);
lean_dec(v_upperBound_1552_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(lean_object* v_upperBound_1559_, lean_object* v_inst_1560_, lean_object* v_R_1561_, lean_object* v_a_1562_, lean_object* v_b_1563_, lean_object* v_c_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1559_, v_a_1562_, v_b_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___boxed(lean_object* v_upperBound_1566_, lean_object* v_inst_1567_, lean_object* v_R_1568_, lean_object* v_a_1569_, lean_object* v_b_1570_, lean_object* v_c_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(v_upperBound_1566_, v_inst_1567_, v_R_1568_, v_a_1569_, v_b_1570_, v_c_1571_);
lean_dec(v_upperBound_1566_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(lean_object* v_as_1573_, size_t v_sz_1574_, size_t v_i_1575_, lean_object* v_b_1576_){
_start:
{
lean_object* v_a_1578_; uint8_t v___x_1582_; 
v___x_1582_ = lean_usize_dec_lt(v_i_1575_, v_sz_1574_);
if (v___x_1582_ == 0)
{
return v_b_1576_;
}
else
{
lean_object* v_a_1583_; lean_object* v_fst_1584_; 
v_a_1583_ = lean_array_uget_borrowed(v_as_1573_, v_i_1575_);
v_fst_1584_ = lean_ctor_get(v_a_1583_, 0);
if (lean_obj_tag(v_fst_1584_) == 1)
{
lean_object* v_val_1585_; lean_object* v_snd_1586_; lean_object* v_s_1587_; lean_object* v_wrap_1588_; lean_object* v___y_1590_; lean_object* v___y_1593_; uint8_t v___x_1604_; 
v_val_1585_ = lean_ctor_get(v_fst_1584_, 0);
v_snd_1586_ = lean_ctor_get(v_a_1583_, 1);
v_s_1587_ = lean_ctor_get(v_val_1585_, 0);
v_wrap_1588_ = lean_ctor_get(v_val_1585_, 1);
v___x_1604_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_s_1587_);
if (v___x_1604_ == 0)
{
uint8_t v___x_1605_; 
v___x_1605_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1586_);
if (v___x_1605_ == 0)
{
lean_object* v_doc_1606_; lean_object* v_doc_1607_; uint8_t v___x_1608_; 
v_doc_1606_ = lean_ctor_get(v_s_1587_, 0);
v_doc_1607_ = lean_ctor_get(v_snd_1586_, 0);
v___x_1608_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1606_);
if (v___x_1608_ == 0)
{
uint8_t v___x_1609_; 
v___x_1609_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1607_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_inc(v_doc_1607_);
lean_inc(v_doc_1606_);
v___x_1610_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1606_, v_doc_1607_);
v___x_1611_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1610_);
v___y_1593_ = v___x_1611_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1612_; 
lean_inc(v_doc_1606_);
v___x_1612_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1606_);
v___y_1593_ = v___x_1612_;
goto v___jp_1592_;
}
}
else
{
lean_object* v___x_1613_; 
lean_inc(v_doc_1607_);
v___x_1613_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1607_);
v___y_1593_ = v___x_1613_;
goto v___jp_1592_;
}
}
else
{
lean_inc_ref(v_s_1587_);
v___y_1593_ = v_s_1587_;
goto v___jp_1592_;
}
}
else
{
lean_inc(v_snd_1586_);
v___y_1593_ = v_snd_1586_;
goto v___jp_1592_;
}
v___jp_1589_:
{
lean_object* v___x_1591_; 
lean_inc_ref(v_wrap_1588_);
v___x_1591_ = lean_apply_1(v_wrap_1588_, v___y_1590_);
v_a_1578_ = v___x_1591_;
goto v___jp_1577_;
}
v___jp_1592_:
{
uint8_t v___x_1594_; 
v___x_1594_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_1593_);
if (v___x_1594_ == 0)
{
uint8_t v___x_1595_; 
v___x_1595_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1576_);
if (v___x_1595_ == 0)
{
lean_object* v_doc_1596_; lean_object* v_doc_1597_; uint8_t v___x_1598_; 
v_doc_1596_ = lean_ctor_get(v___y_1593_, 0);
lean_inc(v_doc_1596_);
lean_dec_ref(v___y_1593_);
v_doc_1597_ = lean_ctor_get(v_b_1576_, 0);
lean_inc(v_doc_1597_);
lean_dec_ref(v_b_1576_);
v___x_1598_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1596_);
if (v___x_1598_ == 0)
{
uint8_t v___x_1599_; 
v___x_1599_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1597_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1596_, v_doc_1597_);
v___x_1601_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1600_);
v___y_1590_ = v___x_1601_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1602_; 
lean_dec(v_doc_1597_);
v___x_1602_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1596_);
v___y_1590_ = v___x_1602_;
goto v___jp_1589_;
}
}
else
{
lean_object* v___x_1603_; 
lean_dec(v_doc_1596_);
v___x_1603_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1597_);
v___y_1590_ = v___x_1603_;
goto v___jp_1589_;
}
}
else
{
lean_dec_ref(v_b_1576_);
v___y_1590_ = v___y_1593_;
goto v___jp_1589_;
}
}
else
{
lean_dec_ref(v___y_1593_);
v___y_1590_ = v_b_1576_;
goto v___jp_1589_;
}
}
}
else
{
lean_object* v_snd_1614_; uint8_t v___x_1615_; 
v_snd_1614_ = lean_ctor_get(v_a_1583_, 1);
v___x_1615_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_snd_1614_);
if (v___x_1615_ == 0)
{
uint8_t v___x_1616_; 
v___x_1616_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_b_1576_);
if (v___x_1616_ == 0)
{
lean_object* v_doc_1617_; lean_object* v_doc_1618_; uint8_t v___x_1619_; 
v_doc_1617_ = lean_ctor_get(v_snd_1614_, 0);
v_doc_1618_ = lean_ctor_get(v_b_1576_, 0);
lean_inc(v_doc_1618_);
lean_dec_ref(v_b_1576_);
v___x_1619_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1617_);
if (v___x_1619_ == 0)
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_1618_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_inc(v_doc_1617_);
v___x_1621_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_1617_, v_doc_1618_);
v___x_1622_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1621_);
v_a_1578_ = v___x_1622_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1623_; 
lean_dec(v_doc_1618_);
lean_inc(v_doc_1617_);
v___x_1623_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1617_);
v_a_1578_ = v___x_1623_;
goto v___jp_1577_;
}
}
else
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_1618_);
v_a_1578_ = v___x_1624_;
goto v___jp_1577_;
}
}
else
{
lean_dec_ref(v_b_1576_);
lean_inc(v_snd_1614_);
v_a_1578_ = v_snd_1614_;
goto v___jp_1577_;
}
}
else
{
v_a_1578_ = v_b_1576_;
goto v___jp_1577_;
}
}
}
v___jp_1577_:
{
size_t v___x_1579_; size_t v___x_1580_; 
v___x_1579_ = ((size_t)1ULL);
v___x_1580_ = lean_usize_add(v_i_1575_, v___x_1579_);
v_i_1575_ = v___x_1580_;
v_b_1576_ = v_a_1578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0___boxed(lean_object* v_as_1625_, lean_object* v_sz_1626_, lean_object* v_i_1627_, lean_object* v_b_1628_){
_start:
{
size_t v_sz_boxed_1629_; size_t v_i_boxed_1630_; lean_object* v_res_1631_; 
v_sz_boxed_1629_ = lean_unbox_usize(v_sz_1626_);
lean_dec(v_sz_1626_);
v_i_boxed_1630_ = lean_unbox_usize(v_i_1627_);
lean_dec(v_i_1627_);
v_res_1631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v_as_1625_, v_sz_boxed_1629_, v_i_boxed_1630_, v_b_1628_);
lean_dec_ref(v_as_1625_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object* v_cs_1632_){
_start:
{
lean_object* v_entries_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v_entries_1633_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1632_);
v___x_1634_ = lean_array_get_size(v_entries_1633_);
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = lean_nat_dec_eq(v___x_1634_, v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_dec_eq(v___x_1634_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v_entries_1639_; lean_object* v_combined_1640_; lean_object* v___x_1641_; size_t v_sz_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v_entries_1639_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(v_entries_1633_);
v_combined_1640_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1641_ = l_Array_reverse___redArg(v_entries_1639_);
v_sz_1642_ = lean_array_size(v___x_1641_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v___x_1641_, v_sz_1642_, v___x_1643_, v_combined_1640_);
lean_dec_ref(v___x_1641_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; lean_object* v_snd_1646_; lean_object* v_fst_1647_; 
v___x_1645_ = lean_array_fget(v_entries_1633_, v___x_1635_);
lean_dec_ref(v_entries_1633_);
v_snd_1646_ = lean_ctor_get(v___x_1645_, 1);
lean_inc(v_snd_1646_);
lean_dec(v___x_1645_);
v_fst_1647_ = lean_ctor_get(v_snd_1646_, 0);
lean_inc(v_fst_1647_);
lean_dec(v_snd_1646_);
return v_fst_1647_;
}
}
else
{
lean_object* v___x_1648_; 
lean_dec_ref(v_entries_1633_);
v___x_1648_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine___boxed(lean_object* v_cs_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Fmt_TaggedDoc_combine(v_cs_1649_);
lean_dec_ref(v_cs_1649_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object* v_lhs_1651_, lean_object* v_sep_1652_, lean_object* v_rhs_1653_, uint8_t v_allowFlattening_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v_nonStickyDoc_1664_; lean_object* v___x_1665_; 
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v_lhs_1651_);
lean_inc_ref(v_sep_1652_);
lean_inc_ref(v___x_1655_);
v___x_1656_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1655_, v_sep_1652_);
v___x_1657_ = lean_box(0);
lean_inc_ref(v_rhs_1653_);
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_rhs_1653_);
v___x_1659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
lean_ctor_set(v___x_1659_, 2, v___x_1657_);
v___x_1660_ = lean_unsigned_to_nat(2u);
v___x_1661_ = lean_mk_empty_array_with_capacity(v___x_1660_);
lean_inc_ref(v___x_1661_);
v___x_1662_ = lean_array_push(v___x_1661_, v___x_1656_);
v___x_1663_ = lean_array_push(v___x_1662_, v___x_1659_);
v_nonStickyDoc_1664_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1663_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_1653_);
if (lean_obj_tag(v___x_1665_) == 1)
{
lean_object* v_val_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1691_; 
v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1691_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_val_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1691_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_wrap_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1689_; 
v_wrap_1670_ = lean_ctor_get(v_sep_1652_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_sep_1652_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; 
v_unused_1690_ = lean_ctor_get(v_sep_1652_, 0);
lean_dec(v_unused_1690_);
v___x_1672_ = v_sep_1652_;
v_isShared_1673_ = v_isSharedCheck_1689_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_wrap_1670_);
lean_dec(v_sep_1652_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1689_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_stickyVariant_1674_; lean_object* v___x_1675_; lean_object* v_stickySep_1677_; 
v_stickyVariant_1674_ = lean_ctor_get(v_val_1666_, 0);
v___x_1675_ = l_Lean_Fmt_TaggedDoc_space;
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1675_);
v_stickySep_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_wrap_1670_);
v_stickySep_1677_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1655_, v_stickySep_1677_);
lean_inc_ref(v_stickyVariant_1674_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v_stickyVariant_1674_);
v___x_1680_ = v___x_1668_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_stickyVariant_1674_);
v___x_1680_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v_stickyDoc_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1657_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
lean_ctor_set(v___x_1681_, 2, v___x_1657_);
v___x_1682_ = lean_array_push(v___x_1661_, v___x_1678_);
v___x_1683_ = lean_array_push(v___x_1682_, v___x_1681_);
v_stickyDoc_1684_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1683_);
lean_dec_ref(v___x_1683_);
v___x_1685_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_1666_, v_allowFlattening_1654_);
lean_dec(v_val_1666_);
v___x_1686_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_1664_, v_stickyDoc_1684_, v___x_1685_);
lean_dec(v___x_1685_);
return v___x_1686_;
}
}
}
}
}
else
{
lean_dec(v___x_1665_);
lean_dec_ref(v___x_1661_);
lean_dec_ref_known(v___x_1655_, 1);
lean_dec_ref(v_sep_1652_);
return v_nonStickyDoc_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine___boxed(lean_object* v_lhs_1692_, lean_object* v_sep_1693_, lean_object* v_rhs_1694_, lean_object* v_allowFlattening_1695_){
_start:
{
uint8_t v_allowFlattening_boxed_1696_; lean_object* v_res_1697_; 
v_allowFlattening_boxed_1696_ = lean_unbox(v_allowFlattening_1695_);
v_res_1697_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_1692_, v_sep_1693_, v_rhs_1694_, v_allowFlattening_boxed_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object* v_body_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(lean_object* v_f_1700_, size_t v_sz_1701_, size_t v_i_1702_, lean_object* v_bs_1703_){
_start:
{
uint8_t v___x_1704_; 
v___x_1704_ = lean_usize_dec_lt(v_i_1702_, v_sz_1701_);
if (v___x_1704_ == 0)
{
lean_dec_ref(v_f_1700_);
return v_bs_1703_;
}
else
{
lean_object* v_v_1705_; lean_object* v___x_1706_; lean_object* v_bs_x27_1707_; lean_object* v___y_1709_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_v_1705_ = lean_array_uget(v_bs_1703_, v_i_1702_);
v___x_1706_ = lean_unsigned_to_nat(0u);
v_bs_x27_1707_ = lean_array_uset(v_bs_1703_, v_i_1702_, v___x_1706_);
v___x_1714_ = lean_usize_to_nat(v_i_1702_);
v___x_1715_ = lean_unsigned_to_nat(2u);
v___x_1716_ = lean_nat_mod(v___x_1714_, v___x_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_nat_dec_eq(v___x_1716_, v___x_1706_);
lean_dec(v___x_1716_);
if (v___x_1717_ == 0)
{
v___y_1709_ = v_v_1705_;
goto v___jp_1708_;
}
else
{
lean_object* v___x_1718_; 
lean_inc_ref(v_f_1700_);
v___x_1718_ = lean_apply_1(v_f_1700_, v_v_1705_);
v___y_1709_ = v___x_1718_;
goto v___jp_1708_;
}
v___jp_1708_:
{
size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1702_, v___x_1710_);
v___x_1712_ = lean_array_uset(v_bs_x27_1707_, v_i_1702_, v___y_1709_);
v_i_1702_ = v___x_1711_;
v_bs_1703_ = v___x_1712_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg___boxed(lean_object* v_f_1719_, lean_object* v_sz_1720_, lean_object* v_i_1721_, lean_object* v_bs_1722_){
_start:
{
size_t v_sz_boxed_1723_; size_t v_i_boxed_1724_; lean_object* v_res_1725_; 
v_sz_boxed_1723_ = lean_unbox_usize(v_sz_1720_);
lean_dec(v_sz_1720_);
v_i_boxed_1724_ = lean_unbox_usize(v_i_1721_);
lean_dec(v_i_1721_);
v_res_1725_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1719_, v_sz_boxed_1723_, v_i_boxed_1724_, v_bs_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(lean_object* v_a_1726_, lean_object* v_f_1727_){
_start:
{
size_t v_sz_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v_sz_1728_ = lean_array_size(v_a_1726_);
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1727_, v_sz_1728_, v___x_1729_, v_a_1726_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems(lean_object* v_sep_1731_, lean_object* v_a_1732_, lean_object* v_f_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(v_a_1732_, v_f_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___boxed(lean_object* v_sep_1735_, lean_object* v_a_1736_, lean_object* v_f_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems(v_sep_1735_, v_a_1736_, v_f_1737_);
lean_dec_ref(v_sep_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(lean_object* v_f_1739_, lean_object* v_as_1740_, size_t v_sz_1741_, size_t v_i_1742_, lean_object* v_bs_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1739_, v_sz_1741_, v_i_1742_, v_bs_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___boxed(lean_object* v_f_1745_, lean_object* v_as_1746_, lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_bs_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(v_f_1745_, v_as_1746_, v_sz_boxed_1750_, v_i_boxed_1751_, v_bs_1749_);
lean_dec_ref(v_as_1746_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_pushElem(lean_object* v_sep_1753_, lean_object* v_a_1754_, lean_object* v_elem_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1756_ = lean_array_get_size(v_a_1754_);
v___x_1757_ = lean_unsigned_to_nat(2u);
v___x_1758_ = lean_nat_mod(v___x_1756_, v___x_1757_);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = lean_nat_dec_eq(v___x_1758_, v___x_1759_);
lean_dec(v___x_1758_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1761_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_1753_);
v___x_1762_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1761_);
v___x_1763_ = lean_mk_empty_array_with_capacity(v___x_1757_);
v___x_1764_ = lean_array_push(v___x_1763_, v___x_1762_);
v___x_1765_ = lean_array_push(v___x_1764_, v_elem_1755_);
v___x_1766_ = l_Array_append___redArg(v_a_1754_, v___x_1765_);
lean_dec_ref(v___x_1765_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; 
lean_dec_ref(v_sep_1753_);
v___x_1767_ = lean_array_push(v_a_1754_, v_elem_1755_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object* v_a_1768_){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_array_get_size(v_a_1768_);
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_shiftr(v___x_1769_, v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg___boxed(lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1772_);
lean_dec_ref(v_a_1772_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems(lean_object* v_sep_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___boxed(lean_object* v_sep_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems(v_sep_1777_, v_a_1778_);
lean_dec_ref(v_a_1778_);
lean_dec_ref(v_sep_1777_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0(lean_object* v_docs_1780_){
_start:
{
lean_inc_ref(v_docs_1780_);
return v_docs_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0___boxed(lean_object* v_docs_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0(v_docs_1781_);
lean_dec_ref(v_docs_1781_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object* v_sep_1784_){
_start:
{
lean_object* v___f_1785_; 
v___f_1785_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___closed__0));
return v___f_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object* v_sep_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(v_sep_1786_);
lean_dec_ref(v_sep_1786_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(lean_object* v_sep_1788_){
_start:
{
lean_object* v___f_1789_; 
v___f_1789_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___closed__0));
return v___f_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___boxed(lean_object* v_sep_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(v_sep_1790_);
lean_dec_ref(v_sep_1790_);
return v_res_1791_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default(void){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = 0;
return v___x_1792_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited(void){
_start:
{
uint8_t v___x_1793_; 
v___x_1793_ = 0;
return v___x_1793_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(uint8_t v_v_1802_, lean_object* v_x_1803_){
_start:
{
return v_v_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed(lean_object* v_v_1804_, lean_object* v_x_1805_){
_start:
{
uint8_t v_v_boxed_1806_; uint8_t v_res_1807_; lean_object* v_r_1808_; 
v_v_boxed_1806_ = lean_unbox(v_v_1804_);
v_res_1807_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(v_v_boxed_1806_, v_x_1805_);
lean_dec_ref(v_x_1805_);
v_r_1808_ = lean_box(v_res_1807_);
return v_r_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object* v_doc_1810_, uint8_t v_isBracketed_1811_){
_start:
{
lean_object* v___f_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___f_1812_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0));
v___x_1813_ = 0;
v___x_1814_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1815_ = lean_box(v___x_1813_);
v___x_1816_ = lean_box(v_isBracketed_1811_);
v___x_1817_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1815_, v___x_1814_, v_doc_1810_, v___x_1816_, v___f_1812_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___boxed(lean_object* v_doc_1818_, lean_object* v_isBracketed_1819_){
_start:
{
uint8_t v_isBracketed_boxed_1820_; lean_object* v_res_1821_; 
v_isBracketed_boxed_1820_ = lean_unbox(v_isBracketed_1819_);
v_res_1821_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_1818_, v_isBracketed_boxed_1820_);
return v_res_1821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object* v_doc_1822_){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1824_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1823_, v_doc_1822_);
if (lean_obj_tag(v___x_1824_) == 0)
{
uint8_t v___x_1825_; 
v___x_1825_ = 0;
return v___x_1825_;
}
else
{
uint8_t v___x_1826_; 
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = 1;
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isSelfDelimited___boxed(lean_object* v_doc_1827_){
_start:
{
uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_res_1828_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1827_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object* v_doc_1830_){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1832_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1831_, v_doc_1830_);
if (lean_obj_tag(v___x_1832_) == 0)
{
uint8_t v___x_1833_; 
v___x_1833_ = 0;
return v___x_1833_;
}
else
{
lean_object* v_val_1834_; uint8_t v___x_1835_; 
v_val_1834_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_val_1834_);
lean_dec_ref_known(v___x_1832_, 1);
v___x_1835_ = lean_unbox(v_val_1834_);
lean_dec(v_val_1834_);
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isBracketed___boxed(lean_object* v_doc_1836_){
_start:
{
uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_res_1837_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_doc_1836_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default(void){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_box(0);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback(void){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_box(0);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(lean_object* v_v_1849_, lean_object* v_x_1850_){
_start:
{
return v_v_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed(lean_object* v_v_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(v_v_1851_, v_x_1852_);
lean_dec_ref(v_x_1852_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object* v_doc_1855_){
_start:
{
lean_object* v___f_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___f_1856_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0));
v___x_1857_ = lean_box(0);
v___x_1858_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1859_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1857_, v___x_1858_, v_doc_1855_, v___x_1857_, v___f_1856_);
return v___x_1859_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object* v_doc_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1862_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1861_, v_doc_1860_);
if (lean_obj_tag(v___x_1862_) == 0)
{
uint8_t v___x_1863_; 
v___x_1863_ = 0;
return v___x_1863_;
}
else
{
uint8_t v___x_1864_; 
lean_dec_ref_known(v___x_1862_, 1);
v___x_1864_ = 1;
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isRawFallback___boxed(lean_object* v_doc_1865_){
_start:
{
uint8_t v_res_1866_; lean_object* v_r_1867_; 
v_res_1866_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1865_);
v_r_1867_ = lean_box(v_res_1866_);
return v_r_1867_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default(void){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_box(0);
return v___x_1868_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned(void){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_box(0);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0(lean_object* v_v_1878_, lean_object* v_x_1879_){
_start:
{
return v_v_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0___boxed(lean_object* v_v_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0(v_v_1880_, v_x_1881_);
lean_dec_ref(v_x_1881_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object* v_doc_1884_){
_start:
{
lean_object* v___f_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___f_1885_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoAligned___closed__0));
v___x_1886_ = lean_box(0);
v___x_1887_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_));
v___x_1888_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1886_, v___x_1887_, v_doc_1884_, v___x_1886_, v___f_1885_);
return v___x_1888_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isPseudoAligned(lean_object* v_doc_1889_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_));
v___x_1891_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1890_, v_doc_1889_);
if (lean_obj_tag(v___x_1891_) == 0)
{
uint8_t v___x_1892_; 
v___x_1892_ = 0;
return v___x_1892_;
}
else
{
uint8_t v___x_1893_; 
lean_dec_ref_known(v___x_1891_, 1);
v___x_1893_ = 1;
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isPseudoAligned___boxed(lean_object* v_doc_1894_){
_start:
{
uint8_t v_res_1895_; lean_object* v_r_1896_; 
v_res_1895_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_1894_);
v_r_1896_ = lean_box(v_res_1895_);
return v_r_1896_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object* v_doc_1897_){
_start:
{
uint8_t v___x_1898_; 
lean_inc_ref(v_doc_1897_);
v___x_1898_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1897_);
if (v___x_1898_ == 0)
{
uint8_t v___x_1899_; 
v___x_1899_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_doc_1897_);
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; 
v___x_1900_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1897_);
if (v___x_1900_ == 0)
{
uint8_t v___x_1901_; 
v___x_1901_ = 1;
return v___x_1901_;
}
else
{
return v___x_1898_;
}
}
else
{
lean_dec_ref(v_doc_1897_);
return v___x_1898_;
}
}
else
{
lean_dec_ref(v_doc_1897_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_needsAppBrackets___boxed(lean_object* v_doc_1902_){
_start:
{
uint8_t v_res_1903_; lean_object* v_r_1904_; 
v_res_1903_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_doc_1902_);
v_r_1904_ = lean_box(v_res_1903_);
return v_r_1904_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default(void){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented(void){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object* v_indentedVariant_1916_, lean_object* v_dedentedVariant_1917_){
_start:
{
lean_object* v___f_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___f_1918_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0));
v___x_1919_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1920_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1921_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1919_, v___x_1920_, v_indentedVariant_1916_, v_dedentedVariant_1917_, v___f_1918_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object* v_doc_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1924_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1923_, v_doc_1922_);
return v___x_1924_;
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

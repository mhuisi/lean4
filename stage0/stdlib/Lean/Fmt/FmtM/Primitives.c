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
lean_object* l_Lean_Fmt_Doc_full___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_fillSomeUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object*);
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
lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Fmt_TaggedDoc_full___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_full___override___redArg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_TaggedDoc_full___closed__0 = (const lean_object*)&l_Lean_Fmt_TaggedDoc_full___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_full(lean_object*);
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
static const lean_closure_object l_Lean_Fmt_TaggedDoc_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_append, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_full(lean_object* v_d_656_){
_start:
{
lean_object* v___f_657_; lean_object* v___x_658_; 
v___f_657_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_full___closed__0));
v___x_658_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_656_, v___f_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_free(lean_object* v_d_660_){
_start:
{
lean_object* v___f_661_; lean_object* v___x_662_; 
v___f_661_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_free___closed__0));
v___x_662_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_660_, v___f_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded___lam__0(lean_object* v_p_663_, lean_object* v_d_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_663_, v_d_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object* v_p_666_, lean_object* v_d_667_){
_start:
{
lean_object* v___f_668_; lean_object* v___x_669_; 
v___f_668_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_guarded___lam__0), 2, 1);
lean_closure_set(v___f_668_, 0, v_p_666_);
v___x_669_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_667_, v___f_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0(lean_object* v_amount_670_, lean_object* v_d_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = l_Lean_Fmt_DefaultCost_ofFailureFallbackPenalty___redArg(v_amount_670_);
v___x_673_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_672_, v_d_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(lean_object* v_d_674_, lean_object* v_amount_675_){
_start:
{
lean_object* v___f_676_; lean_object* v___x_677_; 
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_676_, 0, v_amount_675_);
v___x_677_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_674_, v___f_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0(lean_object* v_amount_678_, lean_object* v_d_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l_Lean_Fmt_DefaultCost_ofOverflowFallbackPenalty___redArg(v_amount_678_);
v___x_681_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_680_, v_d_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(lean_object* v_d_682_, lean_object* v_amount_683_){
_start:
{
lean_object* v___f_684_; lean_object* v___x_685_; 
v___f_684_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_684_, 0, v_amount_683_);
v___x_685_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_682_, v___f_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0(lean_object* v_amount_686_, lean_object* v_d_687_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l_Lean_Fmt_DefaultCost_ofHeightFallbackPenalty___redArg(v_amount_686_);
v___x_689_ = l_Lean_Fmt_Doc_costing___override___redArg(v___x_688_, v_d_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(lean_object* v_d_690_, lean_object* v_amount_691_){
_start:
{
lean_object* v___f_692_; lean_object* v___x_693_; 
v___f_692_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty___lam__0), 2, 1);
lean_closure_set(v___f_692_, 0, v_amount_691_);
v___x_693_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_d_690_, v___f_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_either(lean_object* v_a_694_, lean_object* v_b_695_){
_start:
{
lean_object* v_doc_696_; lean_object* v_doc_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_doc_696_ = lean_ctor_get(v_a_694_, 0);
lean_inc(v_doc_696_);
lean_dec_ref(v_a_694_);
v_doc_697_ = lean_ctor_get(v_b_695_, 0);
lean_inc(v_doc_697_);
lean_dec_ref(v_b_695_);
v___x_698_ = l_Lean_Fmt_Doc_either___override___redArg(v_doc_696_, v_doc_697_);
v___x_699_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object* v_ds_701_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; 
v___f_702_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_oneOf___closed__0));
v___x_703_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_701_, v___f_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnFailure(lean_object* v_d_704_, lean_object* v_fallback_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v___x_707_ = l_Lean_Fmt_TaggedDoc_withFailureFallbackPenalty(v_fallback_705_, v___x_706_);
v___x_708_ = lean_unsigned_to_nat(2u);
v___x_709_ = lean_mk_empty_array_with_capacity(v___x_708_);
v___x_710_ = lean_array_push(v___x_709_, v_d_704_);
v___x_711_ = lean_array_push(v___x_710_, v___x_707_);
v___x_712_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnOverflow(lean_object* v_d_713_, lean_object* v_fallback_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_fallback_714_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = lean_mk_empty_array_with_capacity(v___x_717_);
v___x_719_ = lean_array_push(v___x_718_, v_d_713_);
v___x_720_ = lean_array_push(v___x_719_, v___x_716_);
v___x_721_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object* v_d_722_, lean_object* v_fallback_723_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v_fallback_723_, v___x_724_);
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = lean_mk_empty_array_with_capacity(v___x_726_);
v___x_728_ = lean_array_push(v___x_727_, v_d_722_);
v___x_729_ = lean_array_push(v___x_728_, v___x_725_);
v___x_730_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object* v_a_731_, lean_object* v_b_732_){
_start:
{
lean_object* v_doc_733_; lean_object* v_doc_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_doc_733_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_doc_733_);
lean_dec_ref(v_a_731_);
v_doc_734_ = lean_ctor_get(v_b_732_, 0);
lean_inc(v_doc_734_);
lean_dec_ref(v_b_732_);
v___x_735_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_733_, v_doc_734_);
v___x_736_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object* v_ds_738_){
_start:
{
lean_object* v___f_739_; lean_object* v___x_740_; 
v___f_739_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_join___closed__0));
v___x_740_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_738_, v___f_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing___lam__0(lean_object* v_sep_741_, lean_object* v_x_742_){
_start:
{
lean_object* v_doc_743_; lean_object* v___x_744_; 
v_doc_743_ = lean_ctor_get(v_sep_741_, 0);
lean_inc(v_doc_743_);
lean_dec_ref(v_sep_741_);
v___x_744_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_doc_743_, v_x_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object* v_sep_745_, lean_object* v_ds_746_){
_start:
{
lean_object* v___f_747_; lean_object* v___x_748_; 
v___f_747_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_joinUsing___lam__0), 2, 1);
lean_closure_set(v___f_747_, 0, v_sep_745_);
v___x_748_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_746_, v___f_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object* v_ds_750_){
_start:
{
lean_object* v___f_751_; lean_object* v___x_752_; 
v___f_751_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fill___closed__0));
v___x_752_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_750_, v___f_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0(lean_object* v_wrap_753_, lean_object* v_d_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v_doc_757_; 
v___x_755_ = l_Lean_Fmt_TaggedDoc_untagged(v_d_754_);
v___x_756_ = lean_apply_1(v_wrap_753_, v___x_755_);
v_doc_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_doc_757_);
lean_dec_ref(v___x_756_);
return v_doc_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1(lean_object* v___f_758_, lean_object* v_x_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_x_759_, v___f_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object* v_ds_761_, lean_object* v_wrap_762_){
_start:
{
lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___x_765_; 
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_763_, 0, v_wrap_762_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__1), 2, 1);
lean_closure_set(v___f_764_, 0, v___f_763_);
v___x_765_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_761_, v___f_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing___lam__0(lean_object* v_sep_766_, lean_object* v_x_767_){
_start:
{
lean_object* v_doc_768_; lean_object* v___x_769_; 
v_doc_768_ = lean_ctor_get(v_sep_766_, 0);
lean_inc(v_doc_768_);
lean_dec_ref(v_sep_766_);
v___x_769_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_doc_768_, v_x_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsing(lean_object* v_sep_770_, lean_object* v_ds_771_){
_start:
{
lean_object* v___f_772_; lean_object* v___x_773_; 
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsing___lam__0), 2, 1);
lean_closure_set(v___f_772_, 0, v_sep_770_);
v___x_773_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_771_, v___f_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object* v_ds_775_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; 
v___f_776_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_fillUsingSpace___closed__0));
v___x_777_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_775_, v___f_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1(lean_object* v___f_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_x_779_, v___f_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object* v_ds_781_, lean_object* v_wrap_782_){
_start:
{
lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; 
v___f_783_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_783_, 0, v_wrap_782_);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping___lam__1), 2, 1);
lean_closure_set(v___f_784_, 0, v___f_783_);
v___x_785_ = l_Lean_Fmt_TaggedDoc_propagateArrayMetaData(v_ds_781_, v___f_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(size_t v_sz_786_, size_t v_i_787_, lean_object* v_bs_788_){
_start:
{
uint8_t v___x_789_; 
v___x_789_ = lean_usize_dec_lt(v_i_787_, v_sz_786_);
if (v___x_789_ == 0)
{
return v_bs_788_;
}
else
{
lean_object* v_v_790_; lean_object* v_v_791_; uint8_t v_allowFill_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_806_; 
v_v_790_ = lean_array_uget(v_bs_788_, v_i_787_);
v_v_791_ = lean_ctor_get(v_v_790_, 0);
v_allowFill_792_ = lean_ctor_get_uint8(v_v_790_, sizeof(void*)*1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_v_790_);
if (v_isSharedCheck_806_ == 0)
{
v___x_794_ = v_v_790_;
v_isShared_795_ = v_isSharedCheck_806_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_v_791_);
lean_dec(v_v_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_806_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_doc_796_; lean_object* v___x_797_; lean_object* v_bs_x27_798_; lean_object* v___x_800_; 
v_doc_796_ = lean_ctor_get(v_v_791_, 0);
lean_inc(v_doc_796_);
lean_dec(v_v_791_);
v___x_797_ = lean_unsigned_to_nat(0u);
v_bs_x27_798_ = lean_array_uset(v_bs_788_, v_i_787_, v___x_797_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v_doc_796_);
v___x_800_ = v___x_794_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_doc_796_);
lean_ctor_set_uint8(v_reuseFailAlloc_805_, sizeof(void*)*1, v_allowFill_792_);
v___x_800_ = v_reuseFailAlloc_805_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_787_, v___x_801_);
v___x_803_ = lean_array_uset(v_bs_x27_798_, v_i_787_, v___x_800_);
v_i_787_ = v___x_802_;
v_bs_788_ = v___x_803_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0___boxed(lean_object* v_sz_807_, lean_object* v_i_808_, lean_object* v_bs_809_){
_start:
{
size_t v_sz_boxed_810_; size_t v_i_boxed_811_; lean_object* v_res_812_; 
v_sz_boxed_810_ = lean_unbox_usize(v_sz_807_);
lean_dec(v_sz_807_);
v_i_boxed_811_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_boxed_810_, v_i_boxed_811_, v_bs_809_);
return v_res_812_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_814_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsing(lean_object* v_sep_815_, lean_object* v_ds_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_817_ = lean_array_get_size(v_ds_816_);
v___x_818_ = lean_unsigned_to_nat(1u);
v___x_819_ = lean_nat_dec_eq(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v_doc_820_; size_t v_sz_821_; size_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_doc_820_ = lean_ctor_get(v_sep_815_, 0);
lean_inc(v_doc_820_);
lean_dec_ref(v_sep_815_);
v_sz_821_ = lean_array_size(v_ds_816_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_821_, v___x_822_, v_ds_816_);
v___x_824_ = l_Lean_Fmt_Doc_fillSomeUsing___redArg(v_doc_820_, v___x_823_);
v___x_825_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_824_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_v_829_; 
lean_dec_ref(v_sep_815_);
v___x_826_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_array_get(v___x_826_, v_ds_816_, v___x_827_);
lean_dec_ref(v_ds_816_);
v_v_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_v_829_);
lean_dec(v___x_828_);
return v_v_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object* v_ds_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = lean_array_get_size(v_ds_830_);
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_nat_dec_eq(v___x_831_, v___x_832_);
if (v___x_833_ == 0)
{
size_t v_sz_834_; size_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_sz_834_ = lean_array_size(v_ds_830_);
v___x_835_ = ((size_t)0ULL);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_834_, v___x_835_, v_ds_830_);
v___x_837_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v___x_836_);
v___x_838_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_837_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_v_842_; 
v___x_839_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = lean_array_get(v___x_839_, v_ds_830_, v___x_840_);
lean_dec_ref(v_ds_830_);
v_v_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_v_842_);
lean_dec(v___x_841_);
return v_v_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object* v_ds_843_, lean_object* v_wrap_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_array_get_size(v_ds_843_);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_dec_eq(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___f_848_; size_t v_sz_849_; size_t v___x_850_; lean_object* v_ds_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___f_848_ = lean_alloc_closure((void*)(l_Lean_Fmt_TaggedDoc_fillWrapping___lam__0), 2, 1);
lean_closure_set(v___f_848_, 0, v_wrap_844_);
v_sz_849_ = lean_array_size(v_ds_843_);
v___x_850_ = ((size_t)0ULL);
v_ds_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_TaggedDoc_fillSomeUsing_spec__0(v_sz_849_, v___x_850_, v_ds_843_);
v___x_852_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_851_, v___f_848_);
v___x_853_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_852_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_v_857_; 
lean_dec_ref(v_wrap_844_);
v___x_854_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0, &l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_fillSomeUsing___closed__0);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_array_get(v___x_854_, v_ds_843_, v___x_855_);
lean_dec_ref(v_ds_843_);
v_v_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_v_857_);
lean_dec(v___x_856_);
return v_v_857_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object* v_d_858_){
_start:
{
lean_object* v_doc_859_; uint8_t v___x_860_; 
v_doc_859_ = lean_ctor_get(v_d_858_, 0);
v___x_860_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object* v_d_861_){
_start:
{
uint8_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_d_861_);
lean_dec_ref(v_d_861_);
v_r_863_ = lean_box(v_res_862_);
return v_r_863_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(lean_object* v_d_864_){
_start:
{
lean_object* v_doc_865_; uint8_t v___x_866_; 
v_doc_865_ = lean_ctor_get(v_d_864_, 0);
v___x_866_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_doc_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty___boxed(lean_object* v_d_867_){
_start:
{
uint8_t v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l_Lean_Fmt_TaggedDoc_isAlwaysNonEmpty(v_d_867_);
lean_dec_ref(v_d_867_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isCompoundAtomic(lean_object* v_d_870_){
_start:
{
lean_object* v_doc_871_; uint8_t v___x_872_; 
v_doc_871_ = lean_ctor_get(v_d_870_, 0);
v___x_872_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_doc_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isCompoundAtomic___boxed(lean_object* v_d_873_){
_start:
{
uint8_t v_res_874_; lean_object* v_r_875_; 
v_res_874_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_d_873_);
lean_dec_ref(v_d_873_);
v_r_875_ = lean_box(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object* v_d_876_){
_start:
{
lean_object* v_doc_877_; uint8_t v___x_878_; 
v_doc_877_ = lean_ctor_get(v_d_876_, 0);
v___x_878_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_doc_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isAtomic___boxed(lean_object* v_d_879_){
_start:
{
uint8_t v_res_880_; lean_object* v_r_881_; 
v_res_880_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_d_879_);
lean_dec_ref(v_d_879_);
v_r_881_ = lean_box(v_res_880_);
return v_r_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(uint8_t v_x_884_){
_start:
{
switch(v_x_884_)
{
case 0:
{
lean_object* v___x_885_; 
v___x_885_ = lean_unsigned_to_nat(0u);
return v___x_885_;
}
case 1:
{
lean_object* v___x_886_; 
v___x_886_ = lean_unsigned_to_nat(1u);
return v___x_886_;
}
default: 
{
lean_object* v___x_887_; 
v___x_887_ = lean_unsigned_to_nat(2u);
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx___boxed(lean_object* v_x_888_){
_start:
{
uint8_t v_x_boxed_889_; lean_object* v_res_890_; 
v_x_boxed_889_ = lean_unbox(v_x_888_);
v_res_890_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_x_boxed_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(lean_object* v_k_891_){
_start:
{
lean_inc(v_k_891_);
return v_k_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg___boxed(lean_object* v_k_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___redArg(v_k_892_);
lean_dec(v_k_892_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(lean_object* v_motive_894_, lean_object* v_ctorIdx_895_, uint8_t v_t_896_, lean_object* v_h_897_, lean_object* v_k_898_){
_start:
{
lean_inc(v_k_898_);
return v_k_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim___boxed(lean_object* v_motive_899_, lean_object* v_ctorIdx_900_, lean_object* v_t_901_, lean_object* v_h_902_, lean_object* v_k_903_){
_start:
{
uint8_t v_t_boxed_904_; lean_object* v_res_905_; 
v_t_boxed_904_ = lean_unbox(v_t_901_);
v_res_905_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorElim(v_motive_899_, v_ctorIdx_900_, v_t_boxed_904_, v_h_902_, v_k_903_);
lean_dec(v_k_903_);
lean_dec(v_ctorIdx_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(lean_object* v_coequal_906_){
_start:
{
lean_inc(v_coequal_906_);
return v_coequal_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg___boxed(lean_object* v_coequal_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___redArg(v_coequal_907_);
lean_dec(v_coequal_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(lean_object* v_motive_909_, uint8_t v_t_910_, lean_object* v_h_911_, lean_object* v_coequal_912_){
_start:
{
lean_inc(v_coequal_912_);
return v_coequal_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim___boxed(lean_object* v_motive_913_, lean_object* v_t_914_, lean_object* v_h_915_, lean_object* v_coequal_916_){
_start:
{
uint8_t v_t_boxed_917_; lean_object* v_res_918_; 
v_t_boxed_917_ = lean_unbox(v_t_914_);
v_res_918_ = l_Lean_Fmt_TaggedDoc_StickynessKind_coequal_elim(v_motive_913_, v_t_boxed_917_, v_h_915_, v_coequal_916_);
lean_dec(v_coequal_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(lean_object* v_preferSticky_919_){
_start:
{
lean_inc(v_preferSticky_919_);
return v_preferSticky_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg___boxed(lean_object* v_preferSticky_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___redArg(v_preferSticky_920_);
lean_dec(v_preferSticky_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(lean_object* v_motive_922_, uint8_t v_t_923_, lean_object* v_h_924_, lean_object* v_preferSticky_925_){
_start:
{
lean_inc(v_preferSticky_925_);
return v_preferSticky_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim___boxed(lean_object* v_motive_926_, lean_object* v_t_927_, lean_object* v_h_928_, lean_object* v_preferSticky_929_){
_start:
{
uint8_t v_t_boxed_930_; lean_object* v_res_931_; 
v_t_boxed_930_ = lean_unbox(v_t_927_);
v_res_931_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferSticky_elim(v_motive_926_, v_t_boxed_930_, v_h_928_, v_preferSticky_929_);
lean_dec(v_preferSticky_929_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(lean_object* v_preferUnsticky_932_){
_start:
{
lean_inc(v_preferUnsticky_932_);
return v_preferUnsticky_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg___boxed(lean_object* v_preferUnsticky_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___redArg(v_preferUnsticky_933_);
lean_dec(v_preferUnsticky_933_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(lean_object* v_motive_935_, uint8_t v_t_936_, lean_object* v_h_937_, lean_object* v_preferUnsticky_938_){
_start:
{
lean_inc(v_preferUnsticky_938_);
return v_preferUnsticky_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim___boxed(lean_object* v_motive_939_, lean_object* v_t_940_, lean_object* v_h_941_, lean_object* v_preferUnsticky_942_){
_start:
{
uint8_t v_t_boxed_943_; lean_object* v_res_944_; 
v_t_boxed_943_ = lean_unbox(v_t_940_);
v_res_944_ = l_Lean_Fmt_TaggedDoc_StickynessKind_preferUnsticky_elim(v_motive_939_, v_t_boxed_943_, v_h_941_, v_preferUnsticky_942_);
lean_dec(v_preferUnsticky_942_);
return v_res_944_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind_default(void){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = 0;
return v___x_945_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedStickynessKind(void){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = 0;
return v___x_946_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t v_x_947_, uint8_t v_y_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_x_947_);
v___x_950_ = l_Lean_Fmt_TaggedDoc_StickynessKind_ctorIdx(v_y_948_);
v___x_951_ = lean_nat_dec_eq(v___x_949_, v___x_950_);
lean_dec(v___x_950_);
lean_dec(v___x_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq___boxed(lean_object* v_x_952_, lean_object* v_y_953_){
_start:
{
uint8_t v_x_17__boxed_954_; uint8_t v_y_18__boxed_955_; uint8_t v_res_956_; lean_object* v_r_957_; 
v_x_17__boxed_954_ = lean_unbox(v_x_952_);
v_y_18__boxed_955_ = lean_unbox(v_y_953_);
v_res_956_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_x_17__boxed_954_, v_y_18__boxed_955_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0(void){
_start:
{
uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_960_ = 0;
v___x_961_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_962_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_960_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default(void){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0, &l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0_once, _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default___closed__0);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedSticky(void){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___lam__0(lean_object* v_v_976_, lean_object* v_f_977_){
_start:
{
lean_object* v_stickyVariant_978_; uint8_t v_kind_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_987_; 
v_stickyVariant_978_ = lean_ctor_get(v_v_976_, 0);
v_kind_979_ = lean_ctor_get_uint8(v_v_976_, sizeof(void*)*1);
v_isSharedCheck_987_ = !lean_is_exclusive(v_v_976_);
if (v_isSharedCheck_987_ == 0)
{
v___x_981_ = v_v_976_;
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_stickyVariant_978_);
lean_dec(v_v_976_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_987_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = l_Lean_Fmt_TaggedDoc_propagateMetaData(v_stickyVariant_978_, v_f_977_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_986_, sizeof(void*)*1, v_kind_979_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object* v_nonStickyVariant_989_, lean_object* v_stickyVariant_990_, uint8_t v_kind_991_){
_start:
{
lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___f_992_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_sticky___closed__0));
v___x_993_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_994_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_995_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_995_, 0, v_stickyVariant_990_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v_kind_991_);
v___x_996_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_993_, v___x_994_, v_nonStickyVariant_989_, v___x_995_, v___f_992_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_sticky___boxed(lean_object* v_nonStickyVariant_997_, lean_object* v_stickyVariant_998_, lean_object* v_kind_999_){
_start:
{
uint8_t v_kind_boxed_1000_; lean_object* v_res_1001_; 
v_kind_boxed_1000_ = lean_unbox(v_kind_999_);
v_res_1001_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_997_, v_stickyVariant_998_, v_kind_boxed_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object* v_doc_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_1739244372____hygCtx___hyg_16_));
v___x_1004_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1003_, v_doc_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object* v_doc_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_doc_1005_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_box(0);
return v___x_1007_;
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1017_; 
v_val_1008_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1010_ = v___x_1006_;
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_val_1008_);
lean_dec(v___x_1006_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
uint8_t v_kind_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v_kind_1012_ = lean_ctor_get_uint8(v_val_1008_, sizeof(void*)*1);
lean_dec(v_val_1008_);
v___x_1013_ = lean_box(v_kind_1012_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object* v_inner_1018_, lean_object* v_f_1019_, lean_object* v_kind_x3f_1020_){
_start:
{
lean_object* v_nonStickyOuter_1021_; lean_object* v___x_1022_; 
lean_inc_ref(v_f_1019_);
lean_inc_ref(v_inner_1018_);
v_nonStickyOuter_1021_ = lean_apply_1(v_f_1019_, v_inner_1018_);
v___x_1022_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_inner_1018_);
if (lean_obj_tag(v___x_1022_) == 1)
{
lean_object* v_val_1023_; lean_object* v_stickyVariant_1024_; uint8_t v_kind_1025_; lean_object* v_stickyOuter_1026_; 
v_val_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v_stickyVariant_1024_ = lean_ctor_get(v_val_1023_, 0);
lean_inc_ref(v_stickyVariant_1024_);
v_kind_1025_ = lean_ctor_get_uint8(v_val_1023_, sizeof(void*)*1);
lean_dec(v_val_1023_);
v_stickyOuter_1026_ = lean_apply_1(v_f_1019_, v_stickyVariant_1024_);
if (lean_obj_tag(v_kind_x3f_1020_) == 0)
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1021_, v_stickyOuter_1026_, v_kind_1025_);
return v___x_1027_;
}
else
{
lean_object* v_val_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; 
v_val_1028_ = lean_ctor_get(v_kind_x3f_1020_, 0);
v___x_1029_ = lean_unbox(v_val_1028_);
v___x_1030_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyOuter_1021_, v_stickyOuter_1026_, v___x_1029_);
return v___x_1030_;
}
}
else
{
lean_dec(v___x_1022_);
lean_dec_ref(v_f_1019_);
return v_nonStickyOuter_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness___boxed(lean_object* v_inner_1031_, lean_object* v_f_1032_, lean_object* v_kind_x3f_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_inner_1031_, v_f_1032_, v_kind_x3f_1033_);
lean_dec(v_kind_x3f_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx(lean_object* v_x_1035_){
_start:
{
switch(lean_obj_tag(v_x_1035_))
{
case 0:
{
lean_object* v___x_1036_; 
v___x_1036_ = lean_unsigned_to_nat(0u);
return v___x_1036_;
}
case 1:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_unsigned_to_nat(1u);
return v___x_1037_;
}
default: 
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_unsigned_to_nat(2u);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx___boxed(lean_object* v_x_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorIdx(v_x_1039_);
lean_dec(v_x_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(lean_object* v_t_1041_, lean_object* v_k_1042_){
_start:
{
if (lean_obj_tag(v_t_1041_) == 2)
{
uint8_t v_allowFlattening_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_allowFlattening_1043_ = lean_ctor_get_uint8(v_t_1041_, 0);
v___x_1044_ = lean_box(v_allowFlattening_1043_);
v___x_1045_ = lean_apply_1(v_k_1042_, v___x_1044_);
return v___x_1045_;
}
else
{
return v_k_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg___boxed(lean_object* v_t_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1046_, v_k_1047_);
lean_dec(v_t_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(lean_object* v_motive_1049_, lean_object* v_ctorIdx_1050_, lean_object* v_t_1051_, lean_object* v_h_1052_, lean_object* v_k_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1051_, v_k_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___boxed(lean_object* v_motive_1055_, lean_object* v_ctorIdx_1056_, lean_object* v_t_1057_, lean_object* v_h_1058_, lean_object* v_k_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim(v_motive_1055_, v_ctorIdx_1056_, v_t_1057_, v_h_1058_, v_k_1059_);
lean_dec(v_t_1057_);
lean_dec(v_ctorIdx_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(lean_object* v_t_1061_, lean_object* v_coequal_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1061_, v_coequal_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg___boxed(lean_object* v_t_1064_, lean_object* v_coequal_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___redArg(v_t_1064_, v_coequal_1065_);
lean_dec(v_t_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(lean_object* v_motive_1067_, lean_object* v_t_1068_, lean_object* v_h_1069_, lean_object* v_coequal_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1068_, v_coequal_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim___boxed(lean_object* v_motive_1072_, lean_object* v_t_1073_, lean_object* v_h_1074_, lean_object* v_coequal_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_coequal_elim(v_motive_1072_, v_t_1073_, v_h_1074_, v_coequal_1075_);
lean_dec(v_t_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(lean_object* v_t_1077_, lean_object* v_preferUnsticky_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1077_, v_preferUnsticky_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg___boxed(lean_object* v_t_1080_, lean_object* v_preferUnsticky_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___redArg(v_t_1080_, v_preferUnsticky_1081_);
lean_dec(v_t_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(lean_object* v_motive_1083_, lean_object* v_t_1084_, lean_object* v_h_1085_, lean_object* v_preferUnsticky_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1084_, v_preferUnsticky_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim___boxed(lean_object* v_motive_1088_, lean_object* v_t_1089_, lean_object* v_h_1090_, lean_object* v_preferUnsticky_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferUnsticky_elim(v_motive_1088_, v_t_1089_, v_h_1090_, v_preferUnsticky_1091_);
lean_dec(v_t_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(lean_object* v_t_1093_, lean_object* v_preferSticky_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1093_, v_preferSticky_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg___boxed(lean_object* v_t_1096_, lean_object* v_preferSticky_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___redArg(v_t_1096_, v_preferSticky_1097_);
lean_dec(v_t_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(lean_object* v_motive_1099_, lean_object* v_t_1100_, lean_object* v_h_1101_, lean_object* v_preferSticky_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ctorElim___redArg(v_t_1100_, v_preferSticky_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim___boxed(lean_object* v_motive_1104_, lean_object* v_t_1105_, lean_object* v_h_1106_, lean_object* v_preferSticky_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_preferSticky_elim(v_motive_1104_, v_t_1105_, v_h_1106_, v_preferSticky_1107_);
lean_dec(v_t_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object* v_s_1109_, uint8_t v_allowFlattening_1110_){
_start:
{
uint8_t v_kind_1111_; 
v_kind_1111_ = lean_ctor_get_uint8(v_s_1109_, sizeof(void*)*1);
switch(v_kind_1111_)
{
case 0:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
case 1:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_1113_, 0, v_allowFlattening_1110_);
return v___x_1113_;
}
default: 
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_box(1);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky___boxed(lean_object* v_s_1115_, lean_object* v_allowFlattening_1116_){
_start:
{
uint8_t v_allowFlattening_boxed_1117_; lean_object* v_res_1118_; 
v_allowFlattening_boxed_1117_ = lean_unbox(v_allowFlattening_1116_);
v_res_1118_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_s_1115_, v_allowFlattening_boxed_1117_);
lean_dec_ref(v_s_1115_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object* v_doc_1119_, lean_object* v_stickyDoc_1120_, lean_object* v_cfg_1121_){
_start:
{
switch(lean_obj_tag(v_cfg_1121_))
{
case 0:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1122_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1120_);
v___x_1123_ = lean_unsigned_to_nat(2u);
v___x_1124_ = lean_mk_empty_array_with_capacity(v___x_1123_);
v___x_1125_ = lean_array_push(v___x_1124_, v___x_1122_);
v___x_1126_ = lean_array_push(v___x_1125_, v_doc_1119_);
v___x_1127_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1126_);
return v___x_1127_;
}
case 1:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1128_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1120_);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = l_Lean_Fmt_TaggedDoc_withHeightFallbackPenalty(v___x_1128_, v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(2u);
v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
v___x_1133_ = lean_array_push(v___x_1132_, v_doc_1119_);
v___x_1134_ = lean_array_push(v___x_1133_, v___x_1130_);
v___x_1135_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1134_);
return v___x_1135_;
}
default: 
{
uint8_t v_allowFlattening_1136_; 
v_allowFlattening_1136_ = lean_ctor_get_uint8(v_cfg_1121_, 0);
if (v_allowFlattening_1136_ == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1137_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1120_);
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1119_, v___x_1138_);
v___x_1140_ = lean_unsigned_to_nat(2u);
v___x_1141_ = lean_mk_empty_array_with_capacity(v___x_1140_);
v___x_1142_ = lean_array_push(v___x_1141_, v___x_1137_);
v___x_1143_ = lean_array_push(v___x_1142_, v___x_1139_);
v___x_1144_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1143_);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1145_ = l_Lean_Fmt_TaggedDoc_unflattenable(v_stickyDoc_1120_);
lean_inc_ref(v_doc_1119_);
v___x_1146_ = l_Lean_Fmt_TaggedDoc_flattened(v_doc_1119_);
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = l_Lean_Fmt_TaggedDoc_withOverflowFallbackPenalty(v_doc_1119_, v___x_1147_);
v___x_1149_ = lean_unsigned_to_nat(3u);
v___x_1150_ = lean_mk_empty_array_with_capacity(v___x_1149_);
v___x_1151_ = lean_array_push(v___x_1150_, v___x_1145_);
v___x_1152_ = lean_array_push(v___x_1151_, v___x_1146_);
v___x_1153_ = lean_array_push(v___x_1152_, v___x_1148_);
v___x_1154_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1153_);
return v___x_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt___boxed(lean_object* v_doc_1155_, lean_object* v_stickyDoc_1156_, lean_object* v_cfg_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1155_, v_stickyDoc_1156_, v_cfg_1157_);
lean_dec(v_cfg_1157_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0(lean_object* v_s_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeSep___lam__0___closed__0));
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_s_1160_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOptionComponent___lam__0(lean_object* v_doc_x3f_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
lean_ctor_set(v___x_1167_, 1, v_doc_x3f_1165_);
lean_ctor_set(v___x_1167_, 2, v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object* v_doc_x3f_1170_, lean_object* v_sepBefore_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_sepBefore_1171_);
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v_doc_x3f_1170_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object* v_doc_x3f_1175_, lean_object* v_sepAfter_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1177_ = lean_box(0);
v___x_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1178_, 0, v_sepAfter_1176_);
v___x_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v_doc_x3f_1175_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(lean_object* v_as_1180_, size_t v_i_1181_, size_t v_stop_1182_, lean_object* v_b_1183_){
_start:
{
lean_object* v___y_1185_; uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_eq(v_i_1181_, v_stop_1182_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v_doc_x3f_1191_; 
v___x_1190_ = lean_array_uget_borrowed(v_as_1180_, v_i_1181_);
v_doc_x3f_1191_ = lean_ctor_get(v___x_1190_, 1);
if (lean_obj_tag(v_doc_x3f_1191_) == 0)
{
v___y_1185_ = v_b_1183_;
goto v___jp_1184_;
}
else
{
lean_object* v_sepBefore_x3f_1192_; lean_object* v_sepAfter_x3f_1193_; lean_object* v_val_1194_; uint8_t v___x_1195_; 
v_sepBefore_x3f_1192_ = lean_ctor_get(v___x_1190_, 0);
v_sepAfter_x3f_1193_ = lean_ctor_get(v___x_1190_, 2);
v_val_1194_ = lean_ctor_get(v_doc_x3f_1191_, 0);
v___x_1195_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_inc(v_sepAfter_x3f_1193_);
lean_inc(v_val_1194_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_val_1194_);
lean_ctor_set(v___x_1196_, 1, v_sepAfter_x3f_1193_);
lean_inc(v_sepBefore_x3f_1192_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_sepBefore_x3f_1192_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_array_push(v_b_1183_, v___x_1197_);
v___y_1185_ = v___x_1198_;
goto v___jp_1184_;
}
else
{
v___y_1185_ = v_b_1183_;
goto v___jp_1184_;
}
}
}
else
{
return v_b_1183_;
}
v___jp_1184_:
{
size_t v___x_1186_; size_t v___x_1187_; 
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1181_, v___x_1186_);
v_i_1181_ = v___x_1187_;
v_b_1183_ = v___y_1185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0___boxed(lean_object* v_as_1199_, lean_object* v_i_1200_, lean_object* v_stop_1201_, lean_object* v_b_1202_){
_start:
{
size_t v_i_boxed_1203_; size_t v_stop_boxed_1204_; lean_object* v_res_1205_; 
v_i_boxed_1203_ = lean_unbox_usize(v_i_1200_);
lean_dec(v_i_1200_);
v_stop_boxed_1204_ = lean_unbox_usize(v_stop_1201_);
lean_dec(v_stop_1201_);
v_res_1205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1199_, v_i_boxed_1203_, v_stop_boxed_1204_, v_b_1202_);
lean_dec_ref(v_as_1199_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(lean_object* v_as_1208_, lean_object* v_start_1209_, lean_object* v_stop_1210_){
_start:
{
lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___closed__0));
v___x_1212_ = lean_nat_dec_lt(v_start_1209_, v_stop_1210_);
if (v___x_1212_ == 0)
{
return v___x_1211_;
}
else
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_array_get_size(v_as_1208_);
v___x_1214_ = lean_nat_dec_le(v_stop_1210_, v___x_1213_);
if (v___x_1214_ == 0)
{
uint8_t v___x_1215_; 
v___x_1215_ = lean_nat_dec_lt(v_start_1209_, v___x_1213_);
if (v___x_1215_ == 0)
{
return v___x_1211_;
}
else
{
size_t v___x_1216_; size_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_usize_of_nat(v_start_1209_);
v___x_1217_ = lean_usize_of_nat(v___x_1213_);
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1208_, v___x_1216_, v___x_1217_, v___x_1211_);
return v___x_1218_;
}
}
else
{
size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_usize_of_nat(v_start_1209_);
v___x_1220_ = lean_usize_of_nat(v_stop_1210_);
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0_spec__0(v_as_1208_, v___x_1219_, v___x_1220_, v___x_1211_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0___boxed(lean_object* v_as_1222_, lean_object* v_start_1223_, lean_object* v_stop_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_as_1222_, v_start_1223_, v_stop_1224_);
lean_dec(v_stop_1224_);
lean_dec(v_start_1223_);
lean_dec_ref(v_as_1222_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(lean_object* v_cs_1226_){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_array_get_size(v_cs_1226_);
v___x_1229_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs_spec__0(v_cs_1226_, v___x_1227_, v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs___boxed(lean_object* v_cs_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1230_);
lean_dec_ref(v_cs_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(size_t v_sz_1232_, size_t v_i_1233_, lean_object* v_bs_1234_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1233_, v_sz_1232_);
if (v___x_1235_ == 0)
{
return v_bs_1234_;
}
else
{
lean_object* v_v_1236_; lean_object* v_snd_1237_; lean_object* v_fst_1238_; lean_object* v_fst_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1252_; 
v_v_1236_ = lean_array_uget_borrowed(v_bs_1234_, v_i_1233_);
v_snd_1237_ = lean_ctor_get(v_v_1236_, 1);
lean_inc(v_snd_1237_);
v_fst_1238_ = lean_ctor_get(v_v_1236_, 0);
lean_inc(v_fst_1238_);
v_fst_1239_ = lean_ctor_get(v_snd_1237_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_snd_1237_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_snd_1237_, 1);
lean_dec(v_unused_1253_);
v___x_1241_ = v_snd_1237_;
v_isShared_1242_ = v_isSharedCheck_1252_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_fst_1239_);
lean_dec(v_snd_1237_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1252_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v_bs_x27_1244_; lean_object* v___x_1246_; 
v___x_1243_ = lean_unsigned_to_nat(0u);
v_bs_x27_1244_ = lean_array_uset(v_bs_1234_, v_i_1233_, v___x_1243_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_fst_1239_);
lean_ctor_set(v___x_1241_, 0, v_fst_1238_);
v___x_1246_ = v___x_1241_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_fst_1238_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_fst_1239_);
v___x_1246_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((size_t)1ULL);
v___x_1248_ = lean_usize_add(v_i_1233_, v___x_1247_);
v___x_1249_ = lean_array_uset(v_bs_x27_1244_, v_i_1233_, v___x_1246_);
v_i_1233_ = v___x_1248_;
v_bs_1234_ = v___x_1249_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0___boxed(lean_object* v_sz_1254_, lean_object* v_i_1255_, lean_object* v_bs_1256_){
_start:
{
size_t v_sz_boxed_1257_; size_t v_i_boxed_1258_; lean_object* v_res_1259_; 
v_sz_boxed_1257_ = lean_unbox_usize(v_sz_1254_);
lean_dec(v_sz_1254_);
v_i_boxed_1258_ = lean_unbox_usize(v_i_1255_);
lean_dec(v_i_1255_);
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_boxed_1257_, v_i_boxed_1258_, v_bs_1256_);
return v_res_1259_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v___x_1260_);
return v___x_1262_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__0);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___x_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(lean_object* v_upperBound_1266_, lean_object* v_a_1267_, lean_object* v_b_1268_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_nat_dec_lt(v_a_1267_, v_upperBound_1266_);
if (v___x_1269_ == 0)
{
lean_dec(v_a_1267_);
return v_b_1268_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_snd_1272_; lean_object* v_snd_1273_; lean_object* v___x_1274_; lean_object* v_a_1276_; 
v___x_1270_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1271_ = lean_array_get_borrowed(v___x_1270_, v_b_1268_, v_a_1267_);
v_snd_1272_ = lean_ctor_get(v___x_1271_, 1);
v_snd_1273_ = lean_ctor_get(v_snd_1272_, 1);
v___x_1274_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1273_) == 1)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_nat_add(v_a_1267_, v___x_1274_);
v___x_1280_ = lean_array_get_size(v_b_1268_);
v___x_1281_ = lean_nat_dec_lt(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec(v___x_1279_);
v_a_1276_ = v_b_1268_;
goto v___jp_1275_;
}
else
{
lean_object* v_v_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1293_; 
lean_inc_ref(v_snd_1273_);
v_v_1282_ = lean_array_fget(v_b_1268_, v___x_1279_);
v_snd_1283_ = lean_ctor_get(v_v_1282_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_v_1282_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v_v_1282_, 0);
lean_dec(v_unused_1294_);
v___x_1285_ = v_v_1282_;
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_dec(v_v_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1293_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v_xs_x27_1288_; lean_object* v___x_1290_; 
v___x_1287_ = lean_box(0);
v_xs_x27_1288_ = lean_array_fset(v_b_1268_, v___x_1279_, v___x_1287_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_snd_1273_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_snd_1273_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_snd_1283_);
v___x_1290_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_array_fset(v_xs_x27_1288_, v___x_1279_, v___x_1290_);
lean_dec(v___x_1279_);
v_a_1276_ = v___x_1291_;
goto v___jp_1275_;
}
}
}
}
else
{
v_a_1276_ = v_b_1268_;
goto v___jp_1275_;
}
v___jp_1275_:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_nat_add(v_a_1267_, v___x_1274_);
lean_dec(v_a_1267_);
v_a_1267_ = v___x_1277_;
v_b_1268_ = v_a_1276_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___boxed(lean_object* v_upperBound_1295_, lean_object* v_a_1296_, lean_object* v_b_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1295_, v_a_1296_, v_b_1297_);
lean_dec(v_upperBound_1295_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(lean_object* v_upperBound_1299_, lean_object* v_a_1300_, lean_object* v_b_1301_){
_start:
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_nat_dec_lt(v_a_1300_, v_upperBound_1299_);
if (v___x_1302_ == 0)
{
lean_dec(v_a_1300_);
return v_b_1301_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_snd_1306_; lean_object* v_snd_1307_; lean_object* v___x_1308_; lean_object* v_a_1310_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1305_ = lean_array_get_borrowed(v___x_1304_, v_b_1301_, v_a_1300_);
v_snd_1306_ = lean_ctor_get(v___x_1305_, 1);
v_snd_1307_ = lean_ctor_get(v_snd_1306_, 1);
v___x_1308_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1307_) == 1)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_fst_1315_; 
v___x_1313_ = lean_nat_add(v_a_1300_, v___x_1308_);
v___x_1314_ = lean_array_get_borrowed(v___x_1304_, v_b_1301_, v___x_1313_);
lean_dec(v___x_1313_);
v_fst_1315_ = lean_ctor_get(v___x_1314_, 0);
if (lean_obj_tag(v_fst_1315_) == 1)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = lean_array_get_size(v_b_1301_);
v___x_1317_ = lean_nat_dec_lt(v_a_1300_, v___x_1316_);
if (v___x_1317_ == 0)
{
v_a_1310_ = v_b_1301_;
goto v___jp_1309_;
}
else
{
lean_object* v_v_1318_; lean_object* v_snd_1319_; lean_object* v_fst_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1339_; 
v_v_1318_ = lean_array_fget(v_b_1301_, v_a_1300_);
v_snd_1319_ = lean_ctor_get(v_v_1318_, 1);
v_fst_1320_ = lean_ctor_get(v_v_1318_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_v_1318_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1322_ = v_v_1318_;
v_isShared_1323_ = v_isSharedCheck_1339_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_snd_1319_);
lean_inc(v_fst_1320_);
lean_dec(v_v_1318_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1339_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_fst_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1337_; 
v_fst_1324_ = lean_ctor_get(v_snd_1319_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_snd_1319_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_snd_1319_, 1);
lean_dec(v_unused_1338_);
v___x_1326_ = v_snd_1319_;
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_fst_1324_);
lean_dec(v_snd_1319_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v_xs_x27_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_box(0);
v_xs_x27_1329_ = lean_array_fset(v_b_1301_, v_a_1300_, v___x_1328_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v___x_1303_);
v___x_1331_ = v___x_1326_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_fst_1324_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1303_);
v___x_1331_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1331_);
v___x_1333_ = v___x_1322_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_fst_1320_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_array_fset(v_xs_x27_1329_, v_a_1300_, v___x_1333_);
v_a_1310_ = v___x_1334_;
goto v___jp_1309_;
}
}
}
}
}
}
else
{
v_a_1310_ = v_b_1301_;
goto v___jp_1309_;
}
}
else
{
v_a_1310_ = v_b_1301_;
goto v___jp_1309_;
}
v___jp_1309_:
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_nat_add(v_a_1300_, v___x_1308_);
lean_dec(v_a_1300_);
v_a_1300_ = v___x_1311_;
v_b_1301_ = v_a_1310_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg___boxed(lean_object* v_upperBound_1340_, lean_object* v_a_1341_, lean_object* v_b_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1340_, v_a_1341_, v_b_1342_);
lean_dec(v_upperBound_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(lean_object* v_upperBound_1344_, lean_object* v_a_1345_, lean_object* v_b_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_lt(v_a_1345_, v_upperBound_1344_);
if (v___x_1347_ == 0)
{
return v_b_1346_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v_snd_1351_; lean_object* v_snd_1352_; lean_object* v___x_1353_; lean_object* v_a_1355_; 
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg___closed__1);
v___x_1350_ = lean_array_get_borrowed(v___x_1349_, v_b_1346_, v_a_1345_);
v_snd_1351_ = lean_ctor_get(v___x_1350_, 1);
v_snd_1352_ = lean_ctor_get(v_snd_1351_, 1);
v___x_1353_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_snd_1352_) == 1)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_fst_1360_; 
v___x_1358_ = lean_nat_add(v_a_1345_, v___x_1353_);
v___x_1359_ = lean_array_get_borrowed(v___x_1349_, v_b_1346_, v___x_1358_);
lean_dec(v___x_1358_);
v_fst_1360_ = lean_ctor_get(v___x_1359_, 0);
if (lean_obj_tag(v_fst_1360_) == 1)
{
lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = lean_array_get_size(v_b_1346_);
v___x_1362_ = lean_nat_dec_lt(v_a_1345_, v___x_1361_);
if (v___x_1362_ == 0)
{
v_a_1355_ = v_b_1346_;
goto v___jp_1354_;
}
else
{
lean_object* v_v_1363_; lean_object* v_snd_1364_; lean_object* v_fst_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1384_; 
v_v_1363_ = lean_array_fget(v_b_1346_, v_a_1345_);
v_snd_1364_ = lean_ctor_get(v_v_1363_, 1);
v_fst_1365_ = lean_ctor_get(v_v_1363_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_v_1363_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1367_ = v_v_1363_;
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snd_1364_);
lean_inc(v_fst_1365_);
lean_dec(v_v_1363_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1384_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_fst_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1382_; 
v_fst_1369_ = lean_ctor_get(v_snd_1364_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_snd_1364_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_snd_1364_, 1);
lean_dec(v_unused_1383_);
v___x_1371_ = v_snd_1364_;
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_fst_1369_);
lean_dec(v_snd_1364_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1382_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v_xs_x27_1374_; lean_object* v___x_1376_; 
v___x_1373_ = lean_box(0);
v_xs_x27_1374_ = lean_array_fset(v_b_1346_, v_a_1345_, v___x_1373_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1348_);
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_fst_1369_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v___x_1348_);
v___x_1376_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1378_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1376_);
v___x_1378_ = v___x_1367_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_fst_1365_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_array_fset(v_xs_x27_1374_, v_a_1345_, v___x_1378_);
v_a_1355_ = v___x_1379_;
goto v___jp_1354_;
}
}
}
}
}
}
else
{
v_a_1355_ = v_b_1346_;
goto v___jp_1354_;
}
}
else
{
v_a_1355_ = v_b_1346_;
goto v___jp_1354_;
}
v___jp_1354_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_nat_add(v_a_1345_, v___x_1353_);
v___x_1357_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1344_, v___x_1356_, v_a_1355_);
return v___x_1357_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg___boxed(lean_object* v_upperBound_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1385_, v_a_1386_, v_b_1387_);
lean_dec(v_a_1386_);
lean_dec(v_upperBound_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(lean_object* v_entries_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1404_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_array_get_size(v_entries_1389_);
v___x_1433_ = lean_nat_dec_lt(v___x_1390_, v___x_1432_);
if (v___x_1433_ == 0)
{
v___y_1404_ = v_entries_1389_;
goto v___jp_1403_;
}
else
{
lean_object* v_v_1434_; lean_object* v_snd_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1446_; 
v_v_1434_ = lean_array_fget(v_entries_1389_, v___x_1390_);
v_snd_1435_ = lean_ctor_get(v_v_1434_, 1);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_v_1434_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_v_1434_, 0);
lean_dec(v_unused_1447_);
v___x_1437_ = v_v_1434_;
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snd_1435_);
lean_dec(v_v_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v_xs_x27_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1439_ = lean_box(0);
v_xs_x27_1440_ = lean_array_fset(v_entries_1389_, v___x_1390_, v___x_1439_);
v___x_1441_ = lean_box(0);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1441_);
v___x_1443_ = v___x_1437_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_snd_1435_);
v___x_1443_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_array_fset(v_xs_x27_1440_, v___x_1390_, v___x_1443_);
v___y_1404_ = v___x_1444_;
goto v___jp_1403_;
}
}
}
v___jp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; size_t v_sz_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1394_ = lean_array_get_size(v___y_1393_);
v___x_1395_ = lean_nat_sub(v___x_1394_, v___y_1392_);
v___x_1396_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v___x_1395_, v___x_1390_, v___y_1393_);
lean_dec(v___x_1395_);
v___x_1397_ = lean_array_get_size(v___x_1396_);
v___x_1398_ = lean_nat_sub(v___x_1397_, v___y_1392_);
v___x_1399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v___x_1398_, v___x_1390_, v___x_1396_);
lean_dec(v___x_1398_);
v_sz_1400_ = lean_array_size(v___x_1399_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__0(v_sz_1400_, v___x_1401_, v___x_1399_);
return v___x_1402_;
}
v___jp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1405_ = lean_array_get_size(v___y_1404_);
v___x_1406_ = lean_unsigned_to_nat(1u);
v___x_1407_ = lean_nat_sub(v___x_1405_, v___x_1406_);
v___x_1408_ = lean_nat_dec_lt(v___x_1407_, v___x_1405_);
if (v___x_1408_ == 0)
{
lean_dec(v___x_1407_);
v___y_1392_ = v___x_1406_;
v___y_1393_ = v___y_1404_;
goto v___jp_1391_;
}
else
{
lean_object* v_v_1409_; lean_object* v_snd_1410_; lean_object* v_fst_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1431_; 
v_v_1409_ = lean_array_fget(v___y_1404_, v___x_1407_);
v_snd_1410_ = lean_ctor_get(v_v_1409_, 1);
v_fst_1411_ = lean_ctor_get(v_v_1409_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_v_1409_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1413_ = v_v_1409_;
v_isShared_1414_ = v_isSharedCheck_1431_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_snd_1410_);
lean_inc(v_fst_1411_);
lean_dec(v_v_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1431_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_fst_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1429_; 
v_fst_1415_ = lean_ctor_get(v_snd_1410_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_snd_1410_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_snd_1410_, 1);
lean_dec(v_unused_1430_);
v___x_1417_ = v_snd_1410_;
v_isShared_1418_ = v_isSharedCheck_1429_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_fst_1415_);
lean_dec(v_snd_1410_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1429_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v_xs_x27_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1419_ = lean_box(0);
v_xs_x27_1420_ = lean_array_fset(v___y_1404_, v___x_1407_, v___x_1419_);
v___x_1421_ = lean_box(0);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1421_);
v___x_1423_ = v___x_1417_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_fst_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v___x_1423_);
v___x_1425_ = v___x_1413_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fst_1411_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_array_fset(v_xs_x27_1420_, v___x_1407_, v___x_1425_);
lean_dec(v___x_1407_);
v___y_1392_ = v___x_1406_;
v___y_1393_ = v___x_1426_;
goto v___jp_1391_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(lean_object* v_upperBound_1448_, lean_object* v_inst_1449_, lean_object* v_R_1450_, lean_object* v_a_1451_, lean_object* v_b_1452_, lean_object* v_c_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___redArg(v_upperBound_1448_, v_a_1451_, v_b_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1___boxed(lean_object* v_upperBound_1455_, lean_object* v_inst_1456_, lean_object* v_R_1457_, lean_object* v_a_1458_, lean_object* v_b_1459_, lean_object* v_c_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__1(v_upperBound_1455_, v_inst_1456_, v_R_1457_, v_a_1458_, v_b_1459_, v_c_1460_);
lean_dec(v_upperBound_1455_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(lean_object* v_upperBound_1462_, lean_object* v_inst_1463_, lean_object* v_R_1464_, lean_object* v_a_1465_, lean_object* v_b_1466_, lean_object* v_c_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___redArg(v_upperBound_1462_, v_a_1465_, v_b_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2___boxed(lean_object* v_upperBound_1469_, lean_object* v_inst_1470_, lean_object* v_R_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_, lean_object* v_c_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2(v_upperBound_1469_, v_inst_1470_, v_R_1471_, v_a_1472_, v_b_1473_, v_c_1474_);
lean_dec(v_a_1472_);
lean_dec(v_upperBound_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(lean_object* v_upperBound_1476_, lean_object* v_inst_1477_, lean_object* v_R_1478_, lean_object* v_a_1479_, lean_object* v_b_1480_, lean_object* v_c_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___redArg(v_upperBound_1476_, v_a_1479_, v_b_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2___boxed(lean_object* v_upperBound_1483_, lean_object* v_inst_1484_, lean_object* v_R_1485_, lean_object* v_a_1486_, lean_object* v_b_1487_, lean_object* v_c_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps_spec__2_spec__2(v_upperBound_1483_, v_inst_1484_, v_R_1485_, v_a_1486_, v_b_1487_, v_c_1488_);
lean_dec(v_upperBound_1483_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(lean_object* v_as_1490_, size_t v_sz_1491_, size_t v_i_1492_, lean_object* v_b_1493_){
_start:
{
lean_object* v_a_1495_; uint8_t v___x_1499_; 
v___x_1499_ = lean_usize_dec_lt(v_i_1492_, v_sz_1491_);
if (v___x_1499_ == 0)
{
return v_b_1493_;
}
else
{
lean_object* v_a_1500_; lean_object* v_fst_1501_; 
v_a_1500_ = lean_array_uget_borrowed(v_as_1490_, v_i_1492_);
v_fst_1501_ = lean_ctor_get(v_a_1500_, 0);
if (lean_obj_tag(v_fst_1501_) == 1)
{
lean_object* v_val_1502_; lean_object* v_snd_1503_; lean_object* v_s_1504_; lean_object* v_wrap_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v_val_1502_ = lean_ctor_get(v_fst_1501_, 0);
v_snd_1503_ = lean_ctor_get(v_a_1500_, 1);
v_s_1504_ = lean_ctor_get(v_val_1502_, 0);
v_wrap_1505_ = lean_ctor_get(v_val_1502_, 1);
lean_inc(v_snd_1503_);
lean_inc_ref(v_s_1504_);
v___x_1506_ = l_Lean_Fmt_TaggedDoc_append(v_s_1504_, v_snd_1503_);
v___x_1507_ = l_Lean_Fmt_TaggedDoc_append(v___x_1506_, v_b_1493_);
lean_inc_ref(v_wrap_1505_);
v___x_1508_ = lean_apply_1(v_wrap_1505_, v___x_1507_);
v_a_1495_ = v___x_1508_;
goto v___jp_1494_;
}
else
{
lean_object* v_snd_1509_; lean_object* v___x_1510_; 
v_snd_1509_ = lean_ctor_get(v_a_1500_, 1);
lean_inc(v_snd_1509_);
v___x_1510_ = l_Lean_Fmt_TaggedDoc_append(v_snd_1509_, v_b_1493_);
v_a_1495_ = v___x_1510_;
goto v___jp_1494_;
}
}
v___jp_1494_:
{
size_t v___x_1496_; size_t v___x_1497_; 
v___x_1496_ = ((size_t)1ULL);
v___x_1497_ = lean_usize_add(v_i_1492_, v___x_1496_);
v_i_1492_ = v___x_1497_;
v_b_1493_ = v_a_1495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0___boxed(lean_object* v_as_1511_, lean_object* v_sz_1512_, lean_object* v_i_1513_, lean_object* v_b_1514_){
_start:
{
size_t v_sz_boxed_1515_; size_t v_i_boxed_1516_; lean_object* v_res_1517_; 
v_sz_boxed_1515_ = lean_unbox_usize(v_sz_1512_);
lean_dec(v_sz_1512_);
v_i_boxed_1516_ = lean_unbox_usize(v_i_1513_);
lean_dec(v_i_1513_);
v_res_1517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v_as_1511_, v_sz_boxed_1515_, v_i_boxed_1516_, v_b_1514_);
lean_dec_ref(v_as_1511_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object* v_cs_1518_){
_start:
{
lean_object* v_entries_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; 
v_entries_1519_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_filterEmptyDocs(v_cs_1518_);
v___x_1520_ = lean_array_get_size(v_entries_1519_);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_nat_dec_eq(v___x_1520_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_dec_eq(v___x_1520_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v_entries_1525_; lean_object* v_combined_1526_; lean_object* v___x_1527_; size_t v_sz_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
v_entries_1525_ = l___private_Lean_Fmt_FmtM_Primitives_0__Lean_Fmt_TaggedDoc_combine_normalizeSeps(v_entries_1519_);
v_combined_1526_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_1527_ = l_Array_reverse___redArg(v_entries_1525_);
v_sz_1528_ = lean_array_size(v___x_1527_);
v___x_1529_ = ((size_t)0ULL);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_TaggedDoc_combine_spec__0(v___x_1527_, v_sz_1528_, v___x_1529_, v_combined_1526_);
lean_dec_ref(v___x_1527_);
return v___x_1530_;
}
else
{
lean_object* v___x_1531_; lean_object* v_snd_1532_; lean_object* v_fst_1533_; 
v___x_1531_ = lean_array_fget(v_entries_1519_, v___x_1521_);
lean_dec_ref(v_entries_1519_);
v_snd_1532_ = lean_ctor_get(v___x_1531_, 1);
lean_inc(v_snd_1532_);
lean_dec(v___x_1531_);
v_fst_1533_ = lean_ctor_get(v_snd_1532_, 0);
lean_inc(v_fst_1533_);
lean_dec(v_snd_1532_);
return v_fst_1533_;
}
}
else
{
lean_object* v___x_1534_; 
lean_dec_ref(v_entries_1519_);
v___x_1534_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_combine___boxed(lean_object* v_cs_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Fmt_TaggedDoc_combine(v_cs_1535_);
lean_dec_ref(v_cs_1535_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object* v_lhs_1537_, lean_object* v_sep_1538_, lean_object* v_rhs_1539_, uint8_t v_allowFlattening_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_nonStickyDoc_1550_; lean_object* v___x_1551_; 
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v_lhs_1537_);
lean_inc_ref(v_sep_1538_);
lean_inc_ref(v___x_1541_);
v___x_1542_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1541_, v_sep_1538_);
v___x_1543_ = lean_box(0);
lean_inc_ref(v_rhs_1539_);
v___x_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1544_, 0, v_rhs_1539_);
v___x_1545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
lean_ctor_set(v___x_1545_, 2, v___x_1543_);
v___x_1546_ = lean_unsigned_to_nat(2u);
v___x_1547_ = lean_mk_empty_array_with_capacity(v___x_1546_);
lean_inc_ref(v___x_1547_);
v___x_1548_ = lean_array_push(v___x_1547_, v___x_1542_);
v___x_1549_ = lean_array_push(v___x_1548_, v___x_1545_);
v_nonStickyDoc_1550_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1549_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_1539_);
if (lean_obj_tag(v___x_1551_) == 1)
{
lean_object* v_val_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1577_; 
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1577_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_val_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1577_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_wrap_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1575_; 
v_wrap_1556_ = lean_ctor_get(v_sep_1538_, 1);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_sep_1538_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; 
v_unused_1576_ = lean_ctor_get(v_sep_1538_, 0);
lean_dec(v_unused_1576_);
v___x_1558_ = v_sep_1538_;
v_isShared_1559_ = v_isSharedCheck_1575_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_wrap_1556_);
lean_dec(v_sep_1538_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1575_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_stickyVariant_1560_; lean_object* v___x_1561_; lean_object* v_stickySep_1563_; 
v_stickyVariant_1560_ = lean_ctor_get(v_val_1552_, 0);
v___x_1561_ = l_Lean_Fmt_TaggedDoc_space;
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1561_);
v_stickySep_1563_ = v___x_1558_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_wrap_1556_);
v_stickySep_1563_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1541_, v_stickySep_1563_);
lean_inc_ref(v_stickyVariant_1560_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_stickyVariant_1560_);
v___x_1566_ = v___x_1554_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_stickyVariant_1560_);
v___x_1566_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v_stickyDoc_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1567_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1543_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
lean_ctor_set(v___x_1567_, 2, v___x_1543_);
v___x_1568_ = lean_array_push(v___x_1547_, v___x_1564_);
v___x_1569_ = lean_array_push(v___x_1568_, v___x_1567_);
v_stickyDoc_1570_ = l_Lean_Fmt_TaggedDoc_combine(v___x_1569_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_1552_, v_allowFlattening_1540_);
lean_dec(v_val_1552_);
v___x_1572_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_1550_, v_stickyDoc_1570_, v___x_1571_);
lean_dec(v___x_1571_);
return v___x_1572_;
}
}
}
}
}
else
{
lean_dec(v___x_1551_);
lean_dec_ref(v___x_1547_);
lean_dec_ref_known(v___x_1541_, 1);
lean_dec_ref(v_sep_1538_);
return v_nonStickyDoc_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine___boxed(lean_object* v_lhs_1578_, lean_object* v_sep_1579_, lean_object* v_rhs_1580_, lean_object* v_allowFlattening_1581_){
_start:
{
uint8_t v_allowFlattening_boxed_1582_; lean_object* v_res_1583_; 
v_allowFlattening_boxed_1582_ = lean_unbox(v_allowFlattening_1581_);
v_res_1583_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_1578_, v_sep_1579_, v_rhs_1580_, v_allowFlattening_boxed_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object* v_body_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(lean_object* v_f_1586_, size_t v_sz_1587_, size_t v_i_1588_, lean_object* v_bs_1589_){
_start:
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_usize_dec_lt(v_i_1588_, v_sz_1587_);
if (v___x_1590_ == 0)
{
lean_dec_ref(v_f_1586_);
return v_bs_1589_;
}
else
{
lean_object* v_v_1591_; lean_object* v___x_1592_; lean_object* v_bs_x27_1593_; lean_object* v___y_1595_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_v_1591_ = lean_array_uget(v_bs_1589_, v_i_1588_);
v___x_1592_ = lean_unsigned_to_nat(0u);
v_bs_x27_1593_ = lean_array_uset(v_bs_1589_, v_i_1588_, v___x_1592_);
v___x_1600_ = lean_usize_to_nat(v_i_1588_);
v___x_1601_ = lean_unsigned_to_nat(2u);
v___x_1602_ = lean_nat_mod(v___x_1600_, v___x_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_nat_dec_eq(v___x_1602_, v___x_1592_);
lean_dec(v___x_1602_);
if (v___x_1603_ == 0)
{
v___y_1595_ = v_v_1591_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1604_; 
lean_inc_ref(v_f_1586_);
v___x_1604_ = lean_apply_1(v_f_1586_, v_v_1591_);
v___y_1595_ = v___x_1604_;
goto v___jp_1594_;
}
v___jp_1594_:
{
size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1588_, v___x_1596_);
v___x_1598_ = lean_array_uset(v_bs_x27_1593_, v_i_1588_, v___y_1595_);
v_i_1588_ = v___x_1597_;
v_bs_1589_ = v___x_1598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg___boxed(lean_object* v_f_1605_, lean_object* v_sz_1606_, lean_object* v_i_1607_, lean_object* v_bs_1608_){
_start:
{
size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; lean_object* v_res_1611_; 
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1606_);
lean_dec(v_sz_1606_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1607_);
lean_dec(v_i_1607_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1605_, v_sz_boxed_1609_, v_i_boxed_1610_, v_bs_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(lean_object* v_a_1612_, lean_object* v_f_1613_){
_start:
{
size_t v_sz_1614_; size_t v___x_1615_; lean_object* v___x_1616_; 
v_sz_1614_ = lean_array_size(v_a_1612_);
v___x_1615_ = ((size_t)0ULL);
v___x_1616_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1613_, v_sz_1614_, v___x_1615_, v_a_1612_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems(lean_object* v_sep_1617_, lean_object* v_a_1618_, lean_object* v_f_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems___redArg(v_a_1618_, v_f_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_mapElems___boxed(lean_object* v_sep_1621_, lean_object* v_a_1622_, lean_object* v_f_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Fmt_TaggedDoc_SepArray_mapElems(v_sep_1621_, v_a_1622_, v_f_1623_);
lean_dec_ref(v_sep_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(lean_object* v_f_1625_, lean_object* v_as_1626_, size_t v_sz_1627_, size_t v_i_1628_, lean_object* v_bs_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___redArg(v_f_1625_, v_sz_1627_, v_i_1628_, v_bs_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0___boxed(lean_object* v_f_1631_, lean_object* v_as_1632_, lean_object* v_sz_1633_, lean_object* v_i_1634_, lean_object* v_bs_1635_){
_start:
{
size_t v_sz_boxed_1636_; size_t v_i_boxed_1637_; lean_object* v_res_1638_; 
v_sz_boxed_1636_ = lean_unbox_usize(v_sz_1633_);
lean_dec(v_sz_1633_);
v_i_boxed_1637_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_TaggedDoc_SepArray_mapElems_spec__0(v_f_1631_, v_as_1632_, v_sz_boxed_1636_, v_i_boxed_1637_, v_bs_1635_);
lean_dec_ref(v_as_1632_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_pushElem(lean_object* v_sep_1639_, lean_object* v_a_1640_, lean_object* v_elem_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1642_ = lean_array_get_size(v_a_1640_);
v___x_1643_ = lean_unsigned_to_nat(2u);
v___x_1644_ = lean_nat_mod(v___x_1642_, v___x_1643_);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_nat_dec_eq(v___x_1644_, v___x_1645_);
lean_dec(v___x_1644_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1647_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_1639_);
v___x_1648_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_1647_);
v___x_1649_ = lean_mk_empty_array_with_capacity(v___x_1643_);
v___x_1650_ = lean_array_push(v___x_1649_, v___x_1648_);
v___x_1651_ = lean_array_push(v___x_1650_, v_elem_1641_);
v___x_1652_ = l_Array_append___redArg(v_a_1640_, v___x_1651_);
lean_dec_ref(v___x_1651_);
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; 
lean_dec_ref(v_sep_1639_);
v___x_1653_ = lean_array_push(v_a_1640_, v_elem_1641_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_array_get_size(v_a_1654_);
v___x_1656_ = lean_unsigned_to_nat(1u);
v___x_1657_ = lean_nat_shiftr(v___x_1655_, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg___boxed(lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1658_);
lean_dec_ref(v_a_1658_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems(lean_object* v_sep_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems___redArg(v_a_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_SepArray_numElems___boxed(lean_object* v_sep_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Fmt_TaggedDoc_SepArray_numElems(v_sep_1663_, v_a_1664_);
lean_dec_ref(v_a_1664_);
lean_dec_ref(v_sep_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0(lean_object* v_docs_1666_){
_start:
{
lean_inc_ref(v_docs_1666_);
return v_docs_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0___boxed(lean_object* v_docs_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___lam__0(v_docs_1667_);
lean_dec_ref(v_docs_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(lean_object* v_sep_1670_){
_start:
{
lean_object* v___f_1671_; 
v___f_1671_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___closed__0));
return v___f_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___boxed(lean_object* v_sep_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_Fmt_TaggedDoc_instCoeArraySepArray(v_sep_1672_);
lean_dec_ref(v_sep_1672_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(lean_object* v_sep_1674_){
_start:
{
lean_object* v___f_1675_; 
v___f_1675_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instCoeArraySepArray___closed__0));
return v___f_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray___boxed(lean_object* v_sep_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Fmt_TaggedDoc_instCoeOutSepArrayArray(v_sep_1676_);
lean_dec_ref(v_sep_1676_);
return v_res_1677_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited_default(void){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = 0;
return v___x_1678_;
}
}
static uint8_t _init_l_Lean_Fmt_TaggedDoc_instInhabitedSelfDelimited(void){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = 0;
return v___x_1679_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(uint8_t v_v_1688_, lean_object* v_x_1689_){
_start:
{
return v_v_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0___boxed(lean_object* v_v_1690_, lean_object* v_x_1691_){
_start:
{
uint8_t v_v_boxed_1692_; uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_v_boxed_1692_ = lean_unbox(v_v_1690_);
v_res_1693_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited___lam__0(v_v_boxed_1692_, v_x_1691_);
lean_dec_ref(v_x_1691_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object* v_doc_1696_, uint8_t v_isBracketed_1697_){
_start:
{
lean_object* v___f_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___f_1698_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkSelfDelimited___closed__0));
v___x_1699_ = 0;
v___x_1700_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1701_ = lean_box(v___x_1699_);
v___x_1702_ = lean_box(v_isBracketed_1697_);
v___x_1703_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1701_, v___x_1700_, v_doc_1696_, v___x_1702_, v___f_1698_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited___boxed(lean_object* v_doc_1704_, lean_object* v_isBracketed_1705_){
_start:
{
uint8_t v_isBracketed_boxed_1706_; lean_object* v_res_1707_; 
v_isBracketed_boxed_1706_ = lean_unbox(v_isBracketed_1705_);
v_res_1707_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_1704_, v_isBracketed_boxed_1706_);
return v_res_1707_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object* v_doc_1708_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1710_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1709_, v_doc_1708_);
if (lean_obj_tag(v___x_1710_) == 0)
{
uint8_t v___x_1711_; 
v___x_1711_ = 0;
return v___x_1711_;
}
else
{
uint8_t v___x_1712_; 
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = 1;
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isSelfDelimited___boxed(lean_object* v_doc_1713_){
_start:
{
uint8_t v_res_1714_; lean_object* v_r_1715_; 
v_res_1714_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1713_);
v_r_1715_ = lean_box(v_res_1714_);
return v_r_1715_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isBracketed(lean_object* v_doc_1716_){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_697857363____hygCtx___hyg_14_));
v___x_1718_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1717_, v_doc_1716_);
if (lean_obj_tag(v___x_1718_) == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = 0;
return v___x_1719_;
}
else
{
lean_object* v_val_1720_; uint8_t v___x_1721_; 
v_val_1720_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1721_ = lean_unbox(v_val_1720_);
lean_dec(v_val_1720_);
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isBracketed___boxed(lean_object* v_doc_1722_){
_start:
{
uint8_t v_res_1723_; lean_object* v_r_1724_; 
v_res_1723_ = l_Lean_Fmt_TaggedDoc_isBracketed(v_doc_1722_);
v_r_1724_ = lean_box(v_res_1723_);
return v_r_1724_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback_default(void){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_box(0);
return v___x_1725_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedRawFallback(void){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_box(0);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(lean_object* v_v_1735_, lean_object* v_x_1736_){
_start:
{
return v_v_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0___boxed(lean_object* v_v_1737_, lean_object* v_x_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Fmt_TaggedDoc_mkRawFallback___lam__0(v_v_1737_, v_x_1738_);
lean_dec_ref(v_x_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_mkRawFallback(lean_object* v_doc_1741_){
_start:
{
lean_object* v___f_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___f_1742_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_mkRawFallback___closed__0));
v___x_1743_ = lean_box(0);
v___x_1744_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1745_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1743_, v___x_1744_, v_doc_1741_, v___x_1743_, v___f_1742_);
return v___x_1745_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object* v_doc_1746_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2727796885____hygCtx___hyg_13_));
v___x_1748_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1747_, v_doc_1746_);
if (lean_obj_tag(v___x_1748_) == 0)
{
uint8_t v___x_1749_; 
v___x_1749_ = 0;
return v___x_1749_;
}
else
{
uint8_t v___x_1750_; 
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = 1;
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isRawFallback___boxed(lean_object* v_doc_1751_){
_start:
{
uint8_t v_res_1752_; lean_object* v_r_1753_; 
v_res_1752_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1751_);
v_r_1753_ = lean_box(v_res_1752_);
return v_r_1753_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned_default(void){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_box(0);
return v___x_1754_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoAligned(void){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_box(0);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0(lean_object* v_v_1764_, lean_object* v_x_1765_){
_start:
{
return v_v_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0___boxed(lean_object* v_v_1766_, lean_object* v_x_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Fmt_TaggedDoc_pseudoAligned___lam__0(v_v_1766_, v_x_1767_);
lean_dec_ref(v_x_1767_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object* v_doc_1770_){
_start:
{
lean_object* v___f_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___f_1771_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoAligned___closed__0));
v___x_1772_ = lean_box(0);
v___x_1773_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_));
v___x_1774_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1772_, v___x_1773_, v_doc_1770_, v___x_1772_, v___f_1771_);
return v___x_1774_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_isPseudoAligned(lean_object* v_doc_1775_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2686743071____hygCtx___hyg_13_));
v___x_1777_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1776_, v_doc_1775_);
if (lean_obj_tag(v___x_1777_) == 0)
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
return v___x_1778_;
}
else
{
uint8_t v___x_1779_; 
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = 1;
return v___x_1779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_isPseudoAligned___boxed(lean_object* v_doc_1780_){
_start:
{
uint8_t v_res_1781_; lean_object* v_r_1782_; 
v_res_1781_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_1780_);
v_r_1782_ = lean_box(v_res_1781_);
return v_r_1782_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object* v_doc_1783_){
_start:
{
uint8_t v___x_1784_; 
lean_inc_ref(v_doc_1783_);
v___x_1784_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_doc_1783_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
v___x_1785_ = l_Lean_Fmt_TaggedDoc_isCompoundAtomic(v_doc_1783_);
if (v___x_1785_ == 0)
{
uint8_t v___x_1786_; 
v___x_1786_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_doc_1783_);
if (v___x_1786_ == 0)
{
uint8_t v___x_1787_; 
v___x_1787_ = 1;
return v___x_1787_;
}
else
{
return v___x_1784_;
}
}
else
{
lean_dec_ref(v_doc_1783_);
return v___x_1784_;
}
}
else
{
lean_dec_ref(v_doc_1783_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_needsAppBrackets___boxed(lean_object* v_doc_1788_){
_start:
{
uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_res_1789_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_doc_1788_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented_default(void){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_Fmt_TaggedDoc_instInhabitedPseudoDedented(void){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_pseudoDedented(lean_object* v_indentedVariant_1802_, lean_object* v_dedentedVariant_1803_){
_start:
{
lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___f_1804_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_pseudoDedented___closed__0));
v___x_1805_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1806_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1807_ = l_Lean_Fmt_TaggedDoc_addMetaData___redArg(v___x_1805_, v___x_1806_, v_indentedVariant_1802_, v_dedentedVariant_1803_, v___f_1804_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_TaggedDoc_getPseudoDedented_x3f(lean_object* v_doc_1808_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_Fmt_TaggedDoc_instImpl_00___x40_Lean_Fmt_FmtM_Primitives_2951978202____hygCtx___hyg_14_));
v___x_1810_ = l_Lean_Fmt_TaggedDoc_getMetaData_x3f___redArg(v___x_1809_, v_doc_1808_);
return v___x_1810_;
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

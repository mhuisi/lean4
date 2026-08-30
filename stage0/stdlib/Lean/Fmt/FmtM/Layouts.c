// Lean compiler output
// Module: Lean.Fmt.FmtM.Layouts
// Imports: public import Lean.Fmt.FmtM.Primitives import Init.Data import Init.While import Std.Data.Iterators.Producers.Range import Std.Data.Iterators.Combinators.StepSize
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_empty;
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepAfter(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Fmt_TaggedDoc_combine(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_space;
extern lean_object* l_Lean_Fmt_TaggedDoc_hardNl;
extern lean_object* l_Lean_Fmt_TaggedDoc_nl;
lean_object* l_Lean_Fmt_TaggedDoc_maybeFlattened(lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_break;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpace(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_append(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Fmt_TaggedDoc_join(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_joinUsing(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_flattened(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_oneOf(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_nested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(lean_object*);
lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(uint8_t, uint8_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_Component_withSepBefore(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_withStickyAlt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_getSticky_x3f(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isPseudoAligned(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_needsAppBrackets(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_mkSelfDelimited(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_pseudoAligned(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_aligned(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_propagateStickyness(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed(lean_object*);
lean_object* l_Array_popWhile___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fallbackOnHeight(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillWrapping(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_unflattenable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_array___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_array___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Layouts_array___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_array___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_lines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 2}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_lines___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_lines___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value),((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_sepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_sepLines___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepLines___closed__0;
static lean_once_cell_t l_Lean_Fmt_Layouts_sepLines___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepLines___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_sepFill___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepFill___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1;
static lean_once_cell_t l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_retainedWhitespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_retainedWhitespace___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Layouts_retainedWhitespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_retainedWhitespace___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_retainedWhitespace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_isAlwaysEmpty___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__1_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Layouts"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "infixOperator"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "compactFirstOperationAssertion"};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 54, 146, 101, 77, 208, 96, 214)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__4_value),LEAN_SCALAR_PTR_LITERAL(245, 49, 203, 135, 141, 45, 148, 127)}};
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__5_value),LEAN_SCALAR_PTR_LITERAL(186, 171, 99, 10, 123, 142, 237, 98)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value;
static const lean_ctor_object l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__0_value),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__6_value)}};
static const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7 = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7_value;
LEAN_EXPORT const lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion = (const lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_infixOperator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_infixOperator___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_infixOperator___closed__0_value;
static const lean_array_object l_Lean_Fmt_Layouts_infixOperator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_infixOperator___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_infixOperator___closed__1_value;
static const lean_closure_object l_Lean_Fmt_Layouts_infixOperator___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_TaggedDoc_nested, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_infixOperator___closed__2 = (const lean_object*)&l_Lean_Fmt_Layouts_infixOperator___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_bracketed___lam__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_bracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_bracketed___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__0_value;
static const lean_string_object l_Lean_Fmt_Layouts_bracketed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bracketed"};
static const lean_object* l_Lean_Fmt_Layouts_bracketed___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_Layouts_bracketed___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_Layouts_bracketed___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l_Lean_Fmt_Layouts_bracketed___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 54, 146, 101, 77, 208, 96, 214)}};
static const lean_ctor_object l_Lean_Fmt_Layouts_bracketed___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__2_value_aux_2),((lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 47, 17, 23, 254, 49, 25, 181)}};
static const lean_object* l_Lean_Fmt_Layouts_bracketed___closed__2 = (const lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_parens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_parens___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_parens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0;
static lean_once_cell_t l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_keywordSeparated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_keywordSeparated___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_keywordSeparated___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_array___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Layouts_metaApplication___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_Layouts_metaApplication___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_metaApplication___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_pipeOperator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_pipeOperator___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_pipeOperator___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_instInhabitedBlock;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock = (const lean_object*)&l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_blocks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_blocks___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_blocks___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_tuple___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_tuple___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_localSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_localSignature___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_localSignature___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_localSignature___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_binder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_fill___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_binder___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_binder___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_letDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_letDecl___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_letDecl___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_subtype___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_subtype___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_subtype___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Fmt_Layouts_conditional___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Layouts_conditional___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_conditional___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx(lean_object* v_x_1_){
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
default: 
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx(v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(lean_object* v_t_9_, lean_object* v_k_10_){
_start:
{
if (lean_obj_tag(v_t_9_) == 2)
{
uint8_t v_allowFlattening_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v_allowFlattening_11_ = lean_ctor_get_uint8(v_t_9_, 0);
v___x_12_ = lean_box(v_allowFlattening_11_);
v___x_13_ = lean_apply_1(v_k_10_, v___x_12_);
return v___x_13_;
}
else
{
return v_k_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg___boxed(lean_object* v_t_14_, lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_14_, v_k_15_);
lean_dec(v_t_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___boxed(lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_t_25_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(lean_object* v_t_29_, lean_object* v_join_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_29_, v_join_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg___boxed(lean_object* v_t_32_, lean_object* v_join_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(v_t_32_, v_join_33_);
lean_dec(v_t_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_join_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_36_, v_join_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___boxed(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_join_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(v_motive_40_, v_t_41_, v_h_42_, v_join_43_);
lean_dec(v_t_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(lean_object* v_t_45_, lean_object* v_joinUsingSpace_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_45_, v_joinUsingSpace_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg___boxed(lean_object* v_t_48_, lean_object* v_joinUsingSpace_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(v_t_48_, v_joinUsingSpace_49_);
lean_dec(v_t_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_joinUsingSpace_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_52_, v_joinUsingSpace_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_joinUsingSpace_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(v_motive_56_, v_t_57_, v_h_58_, v_joinUsingSpace_59_);
lean_dec(v_t_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_61_, lean_object* v_joinUsingNl_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_61_, v_joinUsingNl_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg___boxed(lean_object* v_t_64_, lean_object* v_joinUsingNl_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(v_t_64_, v_joinUsingNl_65_);
lean_dec(v_t_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_joinUsingNl_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_68_, v_joinUsingNl_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___boxed(lean_object* v_motive_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_joinUsingNl_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(v_motive_72_, v_t_73_, v_h_74_, v_joinUsingNl_75_);
lean_dec(v_t_73_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(lean_object* v_t_77_, lean_object* v_joinUsingBreak_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_77_, v_joinUsingBreak_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg___boxed(lean_object* v_t_80_, lean_object* v_joinUsingBreak_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(v_t_80_, v_joinUsingBreak_81_);
lean_dec(v_t_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(lean_object* v_motive_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_joinUsingBreak_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_84_, v_joinUsingBreak_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___boxed(lean_object* v_motive_88_, lean_object* v_t_89_, lean_object* v_h_90_, lean_object* v_joinUsingBreak_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(v_motive_88_, v_t_89_, v_h_90_, v_joinUsingBreak_91_);
lean_dec(v_t_89_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(lean_object* v_t_93_, lean_object* v_fill_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_93_, v_fill_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg___boxed(lean_object* v_t_96_, lean_object* v_fill_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(v_t_96_, v_fill_97_);
lean_dec(v_t_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_fill_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_100_, v_fill_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___boxed(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_fill_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(v_motive_104_, v_t_105_, v_h_106_, v_fill_107_);
lean_dec(v_t_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(lean_object* v___y_109_){
_start:
{
lean_inc_ref(v___y_109_);
return v___y_109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed(lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(v___y_110_);
lean_dec_ref(v___y_110_);
return v_res_111_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1(void){
_start:
{
lean_object* v___f_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___f_113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_114_ = l_Lean_Fmt_TaggedDoc_space;
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___f_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(size_t v_sz_116_, size_t v_i_117_, lean_object* v_bs_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = lean_usize_dec_lt(v_i_117_, v_sz_116_);
if (v___x_119_ == 0)
{
return v_bs_118_;
}
else
{
lean_object* v_v_120_; lean_object* v___x_121_; lean_object* v_bs_x27_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v_v_120_ = lean_array_uget(v_bs_118_, v_i_117_);
v___x_121_ = lean_unsigned_to_nat(0u);
v_bs_x27_122_ = lean_array_uset(v_bs_118_, v_i_117_, v___x_121_);
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_v_120_);
v___x_124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_125_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_123_, v___x_124_);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_add(v_i_117_, v___x_126_);
v___x_128_ = lean_array_uset(v_bs_x27_122_, v_i_117_, v___x_125_);
v_i_117_ = v___x_127_;
v_bs_118_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___boxed(lean_object* v_sz_130_, lean_object* v_i_131_, lean_object* v_bs_132_){
_start:
{
size_t v_sz_boxed_133_; size_t v_i_boxed_134_; lean_object* v_res_135_; 
v_sz_boxed_133_ = lean_unbox_usize(v_sz_130_);
lean_dec(v_sz_130_);
v_i_boxed_134_ = lean_unbox_usize(v_i_131_);
lean_dec(v_i_131_);
v_res_135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_boxed_133_, v_i_boxed_134_, v_bs_132_);
return v_res_135_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0(void){
_start:
{
lean_object* v___f_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___f_136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_137_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___f_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(size_t v_sz_139_, size_t v_i_140_, lean_object* v_bs_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_usize_dec_lt(v_i_140_, v_sz_139_);
if (v___x_142_ == 0)
{
return v_bs_141_;
}
else
{
lean_object* v_v_143_; lean_object* v___x_144_; lean_object* v_bs_x27_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; size_t v___x_149_; size_t v___x_150_; lean_object* v___x_151_; 
v_v_143_ = lean_array_uget(v_bs_141_, v_i_140_);
v___x_144_ = lean_unsigned_to_nat(0u);
v_bs_x27_145_ = lean_array_uset(v_bs_141_, v_i_140_, v___x_144_);
v___x_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_146_, 0, v_v_143_);
v___x_147_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0);
v___x_148_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_146_, v___x_147_);
v___x_149_ = ((size_t)1ULL);
v___x_150_ = lean_usize_add(v_i_140_, v___x_149_);
v___x_151_ = lean_array_uset(v_bs_x27_145_, v_i_140_, v___x_148_);
v_i_140_ = v___x_150_;
v_bs_141_ = v___x_151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___boxed(lean_object* v_sz_153_, lean_object* v_i_154_, lean_object* v_bs_155_){
_start:
{
size_t v_sz_boxed_156_; size_t v_i_boxed_157_; lean_object* v_res_158_; 
v_sz_boxed_156_ = lean_unbox_usize(v_sz_153_);
lean_dec(v_sz_153_);
v_i_boxed_157_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_boxed_156_, v_i_boxed_157_, v_bs_155_);
return v_res_158_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0(void){
_start:
{
lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___f_159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_160_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___f_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(size_t v_sz_162_, size_t v_i_163_, lean_object* v_bs_164_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = lean_usize_dec_lt(v_i_163_, v_sz_162_);
if (v___x_165_ == 0)
{
return v_bs_164_;
}
else
{
lean_object* v_v_166_; lean_object* v___x_167_; lean_object* v_bs_x27_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; 
v_v_166_ = lean_array_uget(v_bs_164_, v_i_163_);
v___x_167_ = lean_unsigned_to_nat(0u);
v_bs_x27_168_ = lean_array_uset(v_bs_164_, v_i_163_, v___x_167_);
v___x_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_169_, 0, v_v_166_);
v___x_170_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0);
v___x_171_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_169_, v___x_170_);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_add(v_i_163_, v___x_172_);
v___x_174_ = lean_array_uset(v_bs_x27_168_, v_i_163_, v___x_171_);
v_i_163_ = v___x_173_;
v_bs_164_ = v___x_174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___boxed(lean_object* v_sz_176_, lean_object* v_i_177_, lean_object* v_bs_178_){
_start:
{
size_t v_sz_boxed_179_; size_t v_i_boxed_180_; lean_object* v_res_181_; 
v_sz_boxed_179_ = lean_unbox_usize(v_sz_176_);
lean_dec(v_sz_176_);
v_i_boxed_180_ = lean_unbox_usize(v_i_177_);
lean_dec(v_i_177_);
v_res_181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_boxed_179_, v_i_boxed_180_, v_bs_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(lean_object* v_as_182_, size_t v_i_183_, size_t v_stop_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___y_187_; uint8_t v___x_191_; 
v___x_191_ = lean_usize_dec_eq(v_i_183_, v_stop_184_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_array_uget_borrowed(v_as_182_, v_i_183_);
v___x_193_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_inc(v___x_192_);
v___x_194_ = lean_array_push(v_b_185_, v___x_192_);
v___y_187_ = v___x_194_;
goto v___jp_186_;
}
else
{
v___y_187_ = v_b_185_;
goto v___jp_186_;
}
}
else
{
return v_b_185_;
}
v___jp_186_:
{
size_t v___x_188_; size_t v___x_189_; 
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_183_, v___x_188_);
v_i_183_ = v___x_189_;
v_b_185_ = v___y_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5___boxed(lean_object* v_as_195_, lean_object* v_i_196_, lean_object* v_stop_197_, lean_object* v_b_198_){
_start:
{
size_t v_i_boxed_199_; size_t v_stop_boxed_200_; lean_object* v_res_201_; 
v_i_boxed_199_ = lean_unbox_usize(v_i_196_);
lean_dec(v_i_196_);
v_stop_boxed_200_ = lean_unbox_usize(v_stop_197_);
lean_dec(v_stop_197_);
v_res_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_as_195_, v_i_boxed_199_, v_stop_boxed_200_, v_b_198_);
lean_dec_ref(v_as_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5(lean_object* v_as_202_, size_t v_i_203_, size_t v_stop_204_, lean_object* v_b_205_){
_start:
{
lean_object* v___y_207_; uint8_t v___x_211_; 
v___x_211_ = lean_usize_dec_eq(v_i_203_, v_stop_204_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = lean_array_uget_borrowed(v_as_202_, v_i_203_);
v___x_213_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
lean_inc(v___x_212_);
v___x_214_ = lean_array_push(v_b_205_, v___x_212_);
v___y_207_ = v___x_214_;
goto v___jp_206_;
}
else
{
v___y_207_ = v_b_205_;
goto v___jp_206_;
}
}
else
{
return v_b_205_;
}
v___jp_206_:
{
size_t v___x_208_; size_t v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_203_, v___x_208_);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_as_202_, v___x_209_, v_stop_204_, v___y_207_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5___boxed(lean_object* v_as_215_, lean_object* v_i_216_, lean_object* v_stop_217_, lean_object* v_b_218_){
_start:
{
size_t v_i_boxed_219_; size_t v_stop_boxed_220_; lean_object* v_res_221_; 
v_i_boxed_219_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_stop_boxed_220_ = lean_unbox_usize(v_stop_217_);
lean_dec(v_stop_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5(v_as_215_, v_i_boxed_219_, v_stop_boxed_220_, v_b_218_);
lean_dec_ref(v_as_215_);
return v_res_221_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0(void){
_start:
{
lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___f_222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_223_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___f_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(size_t v_sz_225_, size_t v_i_226_, lean_object* v_bs_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_lt(v_i_226_, v_sz_225_);
if (v___x_228_ == 0)
{
return v_bs_227_;
}
else
{
lean_object* v_v_229_; lean_object* v___x_230_; lean_object* v_bs_x27_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; size_t v___x_235_; size_t v___x_236_; lean_object* v___x_237_; 
v_v_229_ = lean_array_uget(v_bs_227_, v_i_226_);
v___x_230_ = lean_unsigned_to_nat(0u);
v_bs_x27_231_ = lean_array_uset(v_bs_227_, v_i_226_, v___x_230_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_v_229_);
v___x_233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0);
v___x_234_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_232_, v___x_233_);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_226_, v___x_235_);
v___x_237_ = lean_array_uset(v_bs_x27_231_, v_i_226_, v___x_234_);
v_i_226_ = v___x_236_;
v_bs_227_ = v___x_237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___boxed(lean_object* v_sz_239_, lean_object* v_i_240_, lean_object* v_bs_241_){
_start:
{
size_t v_sz_boxed_242_; size_t v_i_boxed_243_; lean_object* v_res_244_; 
v_sz_boxed_242_ = lean_unbox_usize(v_sz_239_);
lean_dec(v_sz_239_);
v_i_boxed_243_ = lean_unbox_usize(v_i_240_);
lean_dec(v_i_240_);
v_res_244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_boxed_242_, v_i_boxed_243_, v_bs_241_);
return v_res_244_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0(void){
_start:
{
lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___f_245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_246_ = l_Lean_Fmt_TaggedDoc_break;
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___f_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(size_t v_sz_248_, size_t v_i_249_, lean_object* v_bs_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = lean_usize_dec_lt(v_i_249_, v_sz_248_);
if (v___x_251_ == 0)
{
return v_bs_250_;
}
else
{
lean_object* v_v_252_; lean_object* v___x_253_; lean_object* v_bs_x27_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v___x_260_; 
v_v_252_ = lean_array_uget(v_bs_250_, v_i_249_);
v___x_253_ = lean_unsigned_to_nat(0u);
v_bs_x27_254_ = lean_array_uset(v_bs_250_, v_i_249_, v___x_253_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v_v_252_);
v___x_256_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_257_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_255_, v___x_256_);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_add(v_i_249_, v___x_258_);
v___x_260_ = lean_array_uset(v_bs_x27_254_, v_i_249_, v___x_257_);
v_i_249_ = v___x_259_;
v_bs_250_ = v___x_260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___boxed(lean_object* v_sz_262_, lean_object* v_i_263_, lean_object* v_bs_264_){
_start:
{
size_t v_sz_boxed_265_; size_t v_i_boxed_266_; lean_object* v_res_267_; 
v_sz_boxed_265_ = lean_unbox_usize(v_sz_262_);
lean_dec(v_sz_262_);
v_i_boxed_266_ = lean_unbox_usize(v_i_263_);
lean_dec(v_i_263_);
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_boxed_265_, v_i_boxed_266_, v_bs_264_);
return v_res_267_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_array___closed__1(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_271_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array(lean_object* v_array_272_, lean_object* v_format_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___y_276_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_array_get_size(v_array_272_);
v___x_320_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_321_ = lean_nat_dec_lt(v___x_274_, v___x_319_);
if (v___x_321_ == 0)
{
v___y_276_ = v___x_320_;
goto v___jp_275_;
}
else
{
uint8_t v___x_322_; 
v___x_322_ = lean_nat_dec_le(v___x_319_, v___x_319_);
if (v___x_322_ == 0)
{
if (v___x_321_ == 0)
{
v___y_276_ = v___x_320_;
goto v___jp_275_;
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((size_t)0ULL);
v___x_324_ = lean_usize_of_nat(v___x_319_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5(v_array_272_, v___x_323_, v___x_324_, v___x_320_);
v___y_276_ = v___x_325_;
goto v___jp_275_;
}
}
else
{
size_t v___x_326_; size_t v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((size_t)0ULL);
v___x_327_ = lean_usize_of_nat(v___x_319_);
v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5(v_array_272_, v___x_326_, v___x_327_, v___x_320_);
v___y_276_ = v___x_328_;
goto v___jp_275_;
}
}
v___jp_275_:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_array_get_size(v___y_276_);
v___x_278_ = lean_nat_dec_eq(v___x_277_, v___x_274_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_dec_eq(v___x_277_, v___x_279_);
if (v___x_280_ == 0)
{
switch(lean_obj_tag(v_format_273_))
{
case 0:
{
size_t v_sz_281_; size_t v___x_282_; lean_object* v_terms_283_; lean_object* v___x_284_; 
v_sz_281_ = lean_array_size(v___y_276_);
v___x_282_ = ((size_t)0ULL);
v_terms_283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_281_, v___x_282_, v___y_276_);
v___x_284_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_283_);
lean_dec_ref(v_terms_283_);
return v___x_284_;
}
case 1:
{
size_t v_sz_285_; size_t v___x_286_; lean_object* v_terms_287_; lean_object* v___x_288_; 
v_sz_285_ = lean_array_size(v___y_276_);
v___x_286_ = ((size_t)0ULL);
v_terms_287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_285_, v___x_286_, v___y_276_);
v___x_288_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_287_);
lean_dec_ref(v_terms_287_);
return v___x_288_;
}
case 2:
{
uint8_t v_allowFlattening_289_; 
v_allowFlattening_289_ = lean_ctor_get_uint8(v_format_273_, 0);
if (v_allowFlattening_289_ == 0)
{
size_t v_sz_290_; size_t v___x_291_; lean_object* v_terms_292_; lean_object* v___x_293_; 
v_sz_290_ = lean_array_size(v___y_276_);
v___x_291_ = ((size_t)0ULL);
v_terms_292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_290_, v___x_291_, v___y_276_);
v___x_293_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_292_);
lean_dec_ref(v_terms_292_);
return v___x_293_;
}
else
{
size_t v_sz_294_; size_t v___x_295_; lean_object* v_terms_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_sz_294_ = lean_array_size(v___y_276_);
v___x_295_ = ((size_t)0ULL);
v_terms_296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_294_, v___x_295_, v___y_276_);
v___x_297_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_296_);
lean_dec_ref(v_terms_296_);
v___x_298_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_297_);
return v___x_298_;
}
}
case 3:
{
size_t v_sz_299_; size_t v___x_300_; lean_object* v_terms_301_; lean_object* v___x_302_; 
v_sz_299_ = lean_array_size(v___y_276_);
v___x_300_ = ((size_t)0ULL);
v_terms_301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_299_, v___x_300_, v___y_276_);
v___x_302_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_301_);
lean_dec_ref(v_terms_301_);
return v___x_302_;
}
default: 
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_304_ = lean_nat_dec_lt(v___x_274_, v___x_277_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec_ref(v___y_276_);
v___x_305_ = lean_obj_once(&l_Lean_Fmt_Layouts_array___closed__1, &l_Lean_Fmt_Layouts_array___closed__1_once, _init_l_Lean_Fmt_Layouts_array___closed__1);
return v___x_305_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = lean_nat_dec_le(v___x_277_, v___x_277_);
if (v___x_306_ == 0)
{
if (v___x_304_ == 0)
{
lean_object* v___x_307_; 
lean_dec_ref(v___y_276_);
v___x_307_ = lean_obj_once(&l_Lean_Fmt_Layouts_array___closed__1, &l_Lean_Fmt_Layouts_array___closed__1_once, _init_l_Lean_Fmt_Layouts_array___closed__1);
return v___x_307_;
}
else
{
size_t v___x_308_; size_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = ((size_t)0ULL);
v___x_309_ = lean_usize_of_nat(v___x_277_);
v___x_310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5(v___y_276_, v___x_308_, v___x_309_, v___x_303_);
lean_dec_ref(v___y_276_);
v___x_311_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_310_);
return v___x_311_;
}
}
else
{
size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = ((size_t)0ULL);
v___x_313_ = lean_usize_of_nat(v___x_277_);
v___x_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5(v___y_276_, v___x_312_, v___x_313_, v___x_303_);
lean_dec_ref(v___y_276_);
v___x_315_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_314_);
return v___x_315_;
}
}
}
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_317_ = lean_array_get(v___x_316_, v___y_276_, v___x_274_);
lean_dec_ref(v___y_276_);
return v___x_317_;
}
}
else
{
lean_object* v___x_318_; 
lean_dec_ref(v___y_276_);
v___x_318_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array___boxed(lean_object* v_array_329_, lean_object* v_format_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Fmt_Layouts_array(v_array_329_, v_format_330_);
lean_dec(v_format_330_);
lean_dec_ref(v_array_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines(lean_object* v_lines_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = ((lean_object*)(l_Lean_Fmt_Layouts_lines___closed__0));
v___x_336_ = l_Lean_Fmt_Layouts_array(v_lines_334_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines___boxed(lean_object* v_lines_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Fmt_Layouts_lines(v_lines_337_);
lean_dec_ref(v_lines_337_);
return v_res_338_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_340_ = l_Lean_Fmt_TaggedDoc_append(v___x_339_, v___x_339_);
return v___x_340_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__1(void){
_start:
{
lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___f_341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___f_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(size_t v_sz_344_, size_t v_i_345_, lean_object* v_bs_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = lean_usize_dec_lt(v_i_345_, v_sz_344_);
if (v___x_347_ == 0)
{
return v_bs_346_;
}
else
{
lean_object* v_v_348_; lean_object* v___x_349_; lean_object* v_bs_x27_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v_v_348_ = lean_array_uget(v_bs_346_, v_i_345_);
v___x_349_ = lean_unsigned_to_nat(0u);
v_bs_x27_350_ = lean_array_uset(v_bs_346_, v_i_345_, v___x_349_);
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_v_348_);
v___x_352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__1);
v___x_353_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_351_, v___x_352_);
v___x_354_ = ((size_t)1ULL);
v___x_355_ = lean_usize_add(v_i_345_, v___x_354_);
v___x_356_ = lean_array_uset(v_bs_x27_350_, v_i_345_, v___x_353_);
v_i_345_ = v___x_355_;
v_bs_346_ = v___x_356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___boxed(lean_object* v_sz_358_, lean_object* v_i_359_, lean_object* v_bs_360_){
_start:
{
size_t v_sz_boxed_361_; size_t v_i_boxed_362_; lean_object* v_res_363_; 
v_sz_boxed_361_ = lean_unbox_usize(v_sz_358_);
lean_dec(v_sz_358_);
v_i_boxed_362_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_res_363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_boxed_361_, v_i_boxed_362_, v_bs_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object* v_lines_364_){
_start:
{
size_t v_sz_365_; size_t v___x_366_; lean_object* v_lines_367_; lean_object* v___x_368_; 
v_sz_365_ = lean_array_size(v_lines_364_);
v___x_366_ = ((size_t)0ULL);
v_lines_367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_365_, v___x_366_, v_lines_364_);
v___x_368_ = l_Lean_Fmt_TaggedDoc_combine(v_lines_367_);
lean_dec_ref(v_lines_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic(lean_object* v_terms_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_box(0);
v___x_371_ = l_Lean_Fmt_Layouts_array(v_terms_369_, v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic___boxed(lean_object* v_terms_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Fmt_Layouts_atomic(v_terms_372_);
lean_dec_ref(v_terms_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object* v_terms_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___y_377_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_array_get_size(v_terms_374_);
v___x_386_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_387_ = lean_nat_dec_lt(v___x_375_, v___x_385_);
if (v___x_387_ == 0)
{
v___y_377_ = v___x_386_;
goto v___jp_376_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = lean_nat_dec_le(v___x_385_, v___x_385_);
if (v___x_388_ == 0)
{
if (v___x_387_ == 0)
{
v___y_377_ = v___x_386_;
goto v___jp_376_;
}
else
{
size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; 
v___x_389_ = ((size_t)0ULL);
v___x_390_ = lean_usize_of_nat(v___x_385_);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_terms_374_, v___x_389_, v___x_390_, v___x_386_);
v___y_377_ = v___x_391_;
goto v___jp_376_;
}
}
else
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v___x_392_ = ((size_t)0ULL);
v___x_393_ = lean_usize_of_nat(v___x_385_);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_terms_374_, v___x_392_, v___x_393_, v___x_386_);
v___y_377_ = v___x_394_;
goto v___jp_376_;
}
}
v___jp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_378_ = lean_array_get_size(v___y_377_);
v___x_379_ = lean_unsigned_to_nat(1u);
v___x_380_ = lean_nat_dec_eq(v___x_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = l_Lean_Fmt_Layouts_atomic(v___y_377_);
lean_dec_ref(v___y_377_);
v___x_382_ = l_Lean_Fmt_TaggedDoc_nested(v___x_381_);
return v___x_382_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_384_ = lean_array_get(v___x_383_, v___y_377_, v___x_375_);
lean_dec_ref(v___y_377_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator___boxed(lean_object* v_terms_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v_terms_395_);
lean_dec_ref(v_terms_395_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object* v_terms_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_box(1);
v___x_399_ = l_Lean_Fmt_Layouts_array(v_terms_397_, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic___boxed(lean_object* v_terms_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Fmt_Layouts_spacedAtomic(v_terms_400_);
lean_dec_ref(v_terms_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill(lean_object* v_terms_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_box(4);
v___x_404_ = l_Lean_Fmt_Layouts_array(v_terms_402_, v___x_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill___boxed(lean_object* v_terms_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_Fmt_Layouts_fill(v_terms_405_);
lean_dec_ref(v_terms_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object* v_terms_407_, uint8_t v_spacing_408_){
_start:
{
if (v_spacing_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_box(3);
v___x_410_ = l_Lean_Fmt_Layouts_array(v_terms_407_, v___x_409_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_411_, 0, v_spacing_408_);
v___x_412_ = l_Lean_Fmt_Layouts_array(v_terms_407_, v___x_411_);
lean_dec_ref_known(v___x_411_, 0);
return v___x_412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical___boxed(lean_object* v_terms_413_, lean_object* v_spacing_414_){
_start:
{
uint8_t v_spacing_boxed_415_; lean_object* v_res_416_; 
v_spacing_boxed_415_ = lean_unbox(v_spacing_414_);
v_res_416_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_413_, v_spacing_boxed_415_);
lean_dec_ref(v_terms_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(uint8_t v_x_417_){
_start:
{
switch(v_x_417_)
{
case 0:
{
lean_object* v___x_418_; 
v___x_418_ = lean_unsigned_to_nat(0u);
return v___x_418_;
}
case 1:
{
lean_object* v___x_419_; 
v___x_419_ = lean_unsigned_to_nat(1u);
return v___x_419_;
}
default: 
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(2u);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___boxed(lean_object* v_x_421_){
_start:
{
uint8_t v_x_boxed_422_; lean_object* v_res_423_; 
v_x_boxed_422_ = lean_unbox(v_x_421_);
v_res_423_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(v_x_boxed_422_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(lean_object* v_k_424_){
_start:
{
lean_inc(v_k_424_);
return v_k_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg___boxed(lean_object* v_k_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(v_k_425_);
lean_dec(v_k_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(lean_object* v_motive_427_, lean_object* v_ctorIdx_428_, uint8_t v_t_429_, lean_object* v_h_430_, lean_object* v_k_431_){
_start:
{
lean_inc(v_k_431_);
return v_k_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___boxed(lean_object* v_motive_432_, lean_object* v_ctorIdx_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_k_436_){
_start:
{
uint8_t v_t_boxed_437_; lean_object* v_res_438_; 
v_t_boxed_437_ = lean_unbox(v_t_434_);
v_res_438_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(v_motive_432_, v_ctorIdx_433_, v_t_boxed_437_, v_h_435_, v_k_436_);
lean_dec(v_k_436_);
lean_dec(v_ctorIdx_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(lean_object* v_includeTrailingSep_439_){
_start:
{
lean_inc(v_includeTrailingSep_439_);
return v_includeTrailingSep_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg___boxed(lean_object* v_includeTrailingSep_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(v_includeTrailingSep_440_);
lean_dec(v_includeTrailingSep_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(lean_object* v_motive_442_, uint8_t v_t_443_, lean_object* v_h_444_, lean_object* v_includeTrailingSep_445_){
_start:
{
lean_inc(v_includeTrailingSep_445_);
return v_includeTrailingSep_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___boxed(lean_object* v_motive_446_, lean_object* v_t_447_, lean_object* v_h_448_, lean_object* v_includeTrailingSep_449_){
_start:
{
uint8_t v_t_boxed_450_; lean_object* v_res_451_; 
v_t_boxed_450_ = lean_unbox(v_t_447_);
v_res_451_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(v_motive_446_, v_t_boxed_450_, v_h_448_, v_includeTrailingSep_449_);
lean_dec(v_includeTrailingSep_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(lean_object* v_excludeTrailingSep_452_){
_start:
{
lean_inc(v_excludeTrailingSep_452_);
return v_excludeTrailingSep_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg___boxed(lean_object* v_excludeTrailingSep_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(v_excludeTrailingSep_453_);
lean_dec(v_excludeTrailingSep_453_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(lean_object* v_motive_455_, uint8_t v_t_456_, lean_object* v_h_457_, lean_object* v_excludeTrailingSep_458_){
_start:
{
lean_inc(v_excludeTrailingSep_458_);
return v_excludeTrailingSep_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___boxed(lean_object* v_motive_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_excludeTrailingSep_462_){
_start:
{
uint8_t v_t_boxed_463_; lean_object* v_res_464_; 
v_t_boxed_463_ = lean_unbox(v_t_460_);
v_res_464_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(v_motive_459_, v_t_boxed_463_, v_h_461_, v_excludeTrailingSep_462_);
lean_dec(v_excludeTrailingSep_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(lean_object* v_retainTrailingSep_465_){
_start:
{
lean_inc(v_retainTrailingSep_465_);
return v_retainTrailingSep_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg___boxed(lean_object* v_retainTrailingSep_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(v_retainTrailingSep_466_);
lean_dec(v_retainTrailingSep_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(lean_object* v_motive_468_, uint8_t v_t_469_, lean_object* v_h_470_, lean_object* v_retainTrailingSep_471_){
_start:
{
lean_inc(v_retainTrailingSep_471_);
return v_retainTrailingSep_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___boxed(lean_object* v_motive_472_, lean_object* v_t_473_, lean_object* v_h_474_, lean_object* v_retainTrailingSep_475_){
_start:
{
uint8_t v_t_boxed_476_; lean_object* v_res_477_; 
v_t_boxed_476_ = lean_unbox(v_t_473_);
v_res_477_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(v_motive_472_, v_t_boxed_476_, v_h_474_, v_retainTrailingSep_475_);
lean_dec(v_retainTrailingSep_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(lean_object* v_x_478_){
_start:
{
switch(lean_obj_tag(v_x_478_))
{
case 0:
{
lean_object* v___x_479_; 
v___x_479_ = lean_unsigned_to_nat(0u);
return v___x_479_;
}
case 1:
{
lean_object* v___x_480_; 
v___x_480_ = lean_unsigned_to_nat(1u);
return v___x_480_;
}
default: 
{
lean_object* v___x_481_; 
v___x_481_ = lean_unsigned_to_nat(2u);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___boxed(lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(v_x_482_);
lean_dec_ref(v_x_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(lean_object* v_t_484_, lean_object* v_k_485_){
_start:
{
if (lean_obj_tag(v_t_484_) == 1)
{
uint8_t v_allowFlattening_486_; lean_object* v_afterElem_x3f_487_; uint8_t v_trailingSep_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_allowFlattening_486_ = lean_ctor_get_uint8(v_t_484_, sizeof(void*)*1);
v_afterElem_x3f_487_ = lean_ctor_get(v_t_484_, 0);
lean_inc(v_afterElem_x3f_487_);
v_trailingSep_488_ = lean_ctor_get_uint8(v_t_484_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_484_, 1);
v___x_489_ = lean_box(v_allowFlattening_486_);
v___x_490_ = lean_box(v_trailingSep_488_);
v___x_491_ = lean_apply_3(v_k_485_, v___x_489_, v_afterElem_x3f_487_, v___x_490_);
return v___x_491_;
}
else
{
lean_object* v_afterElem_x3f_492_; lean_object* v_afterSep_x3f_493_; uint8_t v_trailingSep_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_afterElem_x3f_492_ = lean_ctor_get(v_t_484_, 0);
lean_inc(v_afterElem_x3f_492_);
v_afterSep_x3f_493_ = lean_ctor_get(v_t_484_, 1);
lean_inc(v_afterSep_x3f_493_);
v_trailingSep_494_ = lean_ctor_get_uint8(v_t_484_, sizeof(void*)*2);
lean_dec_ref(v_t_484_);
v___x_495_ = lean_box(v_trailingSep_494_);
v___x_496_ = lean_apply_3(v_k_485_, v_afterElem_x3f_492_, v_afterSep_x3f_493_, v___x_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(lean_object* v_motive_497_, lean_object* v_ctorIdx_498_, lean_object* v_t_499_, lean_object* v_h_500_, lean_object* v_k_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_499_, v_k_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___boxed(lean_object* v_motive_503_, lean_object* v_ctorIdx_504_, lean_object* v_t_505_, lean_object* v_h_506_, lean_object* v_k_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(v_motive_503_, v_ctorIdx_504_, v_t_505_, v_h_506_, v_k_507_);
lean_dec(v_ctorIdx_504_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim___redArg(lean_object* v_t_509_, lean_object* v_joinUsingSep_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_509_, v_joinUsingSep_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim(lean_object* v_motive_512_, lean_object* v_t_513_, lean_object* v_h_514_, lean_object* v_joinUsingSep_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_513_, v_joinUsingSep_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_517_, lean_object* v_joinUsingNl_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_517_, v_joinUsingNl_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim(lean_object* v_motive_520_, lean_object* v_t_521_, lean_object* v_h_522_, lean_object* v_joinUsingNl_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_521_, v_joinUsingNl_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim___redArg(lean_object* v_t_525_, lean_object* v_fillUsingSep_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_525_, v_fillUsingSep_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim(lean_object* v_motive_528_, lean_object* v_t_529_, lean_object* v_h_530_, lean_object* v_fillUsingSep_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_529_, v_fillUsingSep_531_);
return v___x_532_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_533_) == 1)
{
uint8_t v_trailingSep_534_; 
v_trailingSep_534_ = lean_ctor_get_uint8(v_x_533_, sizeof(void*)*1 + 1);
return v_trailingSep_534_;
}
else
{
uint8_t v_trailingSep_535_; 
v_trailingSep_535_ = lean_ctor_get_uint8(v_x_533_, sizeof(void*)*2);
return v_trailingSep_535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep___boxed(lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(v_x_536_);
lean_dec_ref(v_x_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(lean_object* v_sepArray_539_, lean_object* v_sep_540_, lean_object* v___x_541_, uint8_t v_trailingSep_542_, lean_object* v_a_543_, lean_object* v_b_544_){
_start:
{
lean_object* v_inner_545_; lean_object* v_next_546_; 
v_inner_545_ = lean_ctor_get(v_a_543_, 2);
lean_inc(v_inner_545_);
v_next_546_ = lean_ctor_get(v_inner_545_, 0);
lean_inc(v_next_546_);
if (lean_obj_tag(v_next_546_) == 0)
{
lean_dec(v_inner_545_);
lean_dec_ref(v_a_543_);
lean_dec_ref(v_sep_540_);
return v_b_544_;
}
else
{
lean_object* v_nextIdx_547_; lean_object* v_n_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_598_; 
v_nextIdx_547_ = lean_ctor_get(v_a_543_, 0);
v_n_548_ = lean_ctor_get(v_a_543_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_a_543_, 2);
lean_dec(v_unused_599_);
v___x_550_ = v_a_543_;
v_isShared_551_ = v_isSharedCheck_598_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_n_548_);
lean_inc(v_nextIdx_547_);
lean_dec(v_a_543_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_598_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_upperBound_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_596_; 
v_upperBound_552_ = lean_ctor_get(v_inner_545_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_inner_545_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_inner_545_, 0);
lean_dec(v_unused_597_);
v___x_554_ = v_inner_545_;
v_isShared_555_ = v_isSharedCheck_596_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_upperBound_552_);
lean_dec(v_inner_545_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_596_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_595_; 
v_val_556_ = lean_ctor_get(v_next_546_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_next_546_);
if (v_isSharedCheck_595_ == 0)
{
v___x_558_ = v_next_546_;
v_isShared_559_ = v_isSharedCheck_595_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v_next_546_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_595_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_560_ = lean_nat_add(v_val_556_, v_nextIdx_547_);
lean_dec(v_nextIdx_547_);
lean_dec(v_val_556_);
v___x_561_ = lean_nat_dec_lt(v___x_560_, v_upperBound_552_);
if (v___x_561_ == 0)
{
lean_dec(v___x_560_);
lean_del_object(v___x_558_);
lean_del_object(v___x_554_);
lean_dec(v_upperBound_552_);
lean_del_object(v___x_550_);
lean_dec(v_n_548_);
lean_dec_ref(v_sep_540_);
return v_b_544_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_562_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v___x_560_, v___x_563_);
lean_inc(v___x_564_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_564_);
v___x_566_ = v___x_558_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_594_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_568_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_566_);
v___x_568_ = v___x_554_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_upperBound_552_);
v___x_568_ = v_reuseFailAlloc_593_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
lean_inc(v_n_548_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 2, v___x_568_);
lean_ctor_set(v___x_550_, 0, v_n_548_);
v___x_570_ = v___x_550_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_n_548_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_n_548_);
lean_ctor_set(v_reuseFailAlloc_592_, 2, v___x_568_);
v___x_570_ = v_reuseFailAlloc_592_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_571_ = lean_array_get_borrowed(v___x_562_, v_sepArray_539_, v___x_560_);
v___x_572_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_571_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; lean_object* v___y_575_; lean_object* v___y_579_; 
lean_inc(v___x_571_);
v___x_573_ = lean_array_push(v_b_544_, v___x_571_);
if (v_trailingSep_542_ == 2)
{
goto v___jp_588_;
}
else
{
if (v___x_572_ == 0)
{
lean_dec(v___x_560_);
goto v___jp_583_;
}
else
{
goto v___jp_588_;
}
}
v___jp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_array_push(v___x_573_, v___y_575_);
v_a_543_ = v___x_570_;
v_b_544_ = v___x_576_;
goto _start;
}
v___jp_578_:
{
uint8_t v___x_580_; 
v___x_580_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_579_);
if (v___x_580_ == 0)
{
v___y_575_ = v___y_579_;
goto v___jp_574_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec_ref(v___y_579_);
lean_inc_ref(v_sep_540_);
v___x_581_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_540_);
v___x_582_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_581_);
v___y_575_ = v___x_582_;
goto v___jp_574_;
}
}
v___jp_583_:
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_array_get_size(v_sepArray_539_);
v___x_585_ = lean_nat_dec_lt(v___x_564_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec(v___x_564_);
v___x_586_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_579_ = v___x_586_;
goto v___jp_578_;
}
else
{
lean_object* v___x_587_; 
v___x_587_ = lean_array_fget_borrowed(v_sepArray_539_, v___x_564_);
lean_dec(v___x_564_);
lean_inc(v___x_587_);
v___y_579_ = v___x_587_;
goto v___jp_578_;
}
}
v___jp_588_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_nat_sub(v___x_541_, v___x_563_);
v___x_590_ = lean_nat_dec_eq(v___x_560_, v___x_589_);
lean_dec(v___x_589_);
lean_dec(v___x_560_);
if (v___x_590_ == 0)
{
goto v___jp_583_;
}
else
{
lean_dec_ref(v___x_570_);
lean_dec(v___x_564_);
lean_dec_ref(v_sep_540_);
return v___x_573_;
}
}
}
else
{
lean_dec(v___x_564_);
lean_dec(v___x_560_);
v_a_543_ = v___x_570_;
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg___boxed(lean_object* v_sepArray_600_, lean_object* v_sep_601_, lean_object* v___x_602_, lean_object* v_trailingSep_603_, lean_object* v_a_604_, lean_object* v_b_605_){
_start:
{
uint8_t v_trailingSep_boxed_606_; lean_object* v_res_607_; 
v_trailingSep_boxed_606_ = lean_unbox(v_trailingSep_603_);
v_res_607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_600_, v_sep_601_, v___x_602_, v_trailingSep_boxed_606_, v_a_604_, v_b_605_);
lean_dec(v___x_602_);
lean_dec_ref(v_sepArray_600_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(lean_object* v_sep_610_, lean_object* v_sepArray_611_, uint8_t v_trailingSep_612_){
_start:
{
lean_object* v___x_613_; lean_object* v_r_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v_r_614_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_615_ = lean_array_get_size(v_sepArray_611_);
v___x_616_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0));
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_619_, 0, v___x_613_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
lean_ctor_set(v___x_619_, 2, v___x_617_);
v___x_620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_611_, v_sep_610_, v___x_615_, v_trailingSep_612_, v___x_619_, v_r_614_);
if (v_trailingSep_612_ == 1)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_621_ = lean_unsigned_to_nat(2u);
v___x_622_ = lean_array_get_size(v___x_620_);
v___x_623_ = lean_nat_mod(v___x_622_, v___x_621_);
v___x_624_ = lean_nat_dec_eq(v___x_623_, v___x_613_);
lean_dec(v___x_623_);
if (v___x_624_ == 0)
{
return v___x_620_;
}
else
{
lean_object* v___x_625_; 
v___x_625_ = lean_array_pop(v___x_620_);
return v___x_625_;
}
}
else
{
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___boxed(lean_object* v_sep_626_, lean_object* v_sepArray_627_, lean_object* v_trailingSep_628_){
_start:
{
uint8_t v_trailingSep_boxed_629_; lean_object* v_res_630_; 
v_trailingSep_boxed_629_ = lean_unbox(v_trailingSep_628_);
v_res_630_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_626_, v_sepArray_627_, v_trailingSep_boxed_629_);
lean_dec_ref(v_sepArray_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(lean_object* v_sepArray_631_, lean_object* v_sep_632_, lean_object* v___x_633_, uint8_t v_trailingSep_634_, lean_object* v_inst_635_, lean_object* v_R_636_, lean_object* v_a_637_, lean_object* v_b_638_, lean_object* v_c_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_631_, v_sep_632_, v___x_633_, v_trailingSep_634_, v_a_637_, v_b_638_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___boxed(lean_object* v_sepArray_641_, lean_object* v_sep_642_, lean_object* v___x_643_, lean_object* v_trailingSep_644_, lean_object* v_inst_645_, lean_object* v_R_646_, lean_object* v_a_647_, lean_object* v_b_648_, lean_object* v_c_649_){
_start:
{
uint8_t v_trailingSep_boxed_650_; lean_object* v_res_651_; 
v_trailingSep_boxed_650_ = lean_unbox(v_trailingSep_644_);
v_res_651_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(v_sepArray_641_, v_sep_642_, v___x_643_, v_trailingSep_boxed_650_, v_inst_645_, v_R_646_, v_a_647_, v_b_648_, v_c_649_);
lean_dec(v___x_643_);
lean_dec_ref(v_sepArray_641_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(lean_object* v_sepArray_652_, lean_object* v_sep_653_, lean_object* v_afterSep_x3f_654_, lean_object* v_afterElem_x3f_655_, size_t v_sz_656_, size_t v_i_657_, lean_object* v_bs_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = lean_usize_dec_lt(v_i_657_, v_sz_656_);
if (v___x_659_ == 0)
{
lean_dec(v_afterElem_x3f_655_);
lean_dec(v_afterSep_x3f_654_);
lean_dec_ref(v_sep_653_);
return v_bs_658_;
}
else
{
lean_object* v_v_660_; lean_object* v___x_661_; lean_object* v_bs_x27_662_; lean_object* v___y_664_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_v_660_ = lean_array_uget(v_bs_658_, v_i_657_);
v___x_661_ = lean_unsigned_to_nat(0u);
v_bs_x27_662_ = lean_array_uset(v_bs_658_, v_i_657_, v___x_661_);
v___x_674_ = lean_usize_to_nat(v_i_657_);
v___x_675_ = lean_array_get_size(v_sepArray_652_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_sub(v___x_675_, v___x_676_);
v___x_678_ = lean_nat_dec_eq(v___x_674_, v___x_677_);
lean_dec(v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v_isElem_681_; lean_object* v___y_683_; 
v___x_679_ = lean_unsigned_to_nat(2u);
v___x_680_ = lean_nat_mod(v___x_674_, v___x_679_);
lean_dec(v___x_674_);
v_isElem_681_ = lean_nat_dec_eq(v___x_680_, v___x_661_);
lean_dec(v___x_680_);
if (v_isElem_681_ == 0)
{
lean_inc(v_afterSep_x3f_654_);
v___y_683_ = v_afterSep_x3f_654_;
goto v___jp_682_;
}
else
{
lean_inc(v_afterElem_x3f_655_);
v___y_683_ = v_afterElem_x3f_655_;
goto v___jp_682_;
}
v___jp_682_:
{
if (v_isElem_681_ == 0)
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_660_);
if (v___x_684_ == 0)
{
v___y_670_ = v___y_683_;
v___y_671_ = v_v_660_;
goto v___jp_669_;
}
else
{
if (v_isElem_681_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec(v_v_660_);
lean_inc_ref(v_sep_653_);
v___x_685_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_653_);
v___x_686_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_685_);
v___y_670_ = v___y_683_;
v___y_671_ = v___x_686_;
goto v___jp_669_;
}
else
{
v___y_670_ = v___y_683_;
v___y_671_ = v_v_660_;
goto v___jp_669_;
}
}
}
else
{
v___y_670_ = v___y_683_;
v___y_671_ = v_v_660_;
goto v___jp_669_;
}
}
}
else
{
lean_dec(v___x_674_);
v___y_664_ = v_v_660_;
goto v___jp_663_;
}
v___jp_663_:
{
size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_657_, v___x_665_);
v___x_667_ = lean_array_uset(v_bs_x27_662_, v_i_657_, v___y_664_);
v_i_657_ = v___x_666_;
v_bs_658_ = v___x_667_;
goto _start;
}
v___jp_669_:
{
if (lean_obj_tag(v___y_670_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; 
v_val_672_ = lean_ctor_get(v___y_670_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v___y_670_, 1);
v___x_673_ = l_Lean_Fmt_TaggedDoc_append(v___y_671_, v_val_672_);
v___y_664_ = v___x_673_;
goto v___jp_663_;
}
else
{
lean_dec(v___y_670_);
v___y_664_ = v___y_671_;
goto v___jp_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg___boxed(lean_object* v_sepArray_687_, lean_object* v_sep_688_, lean_object* v_afterSep_x3f_689_, lean_object* v_afterElem_x3f_690_, lean_object* v_sz_691_, lean_object* v_i_692_, lean_object* v_bs_693_){
_start:
{
size_t v_sz_boxed_694_; size_t v_i_boxed_695_; lean_object* v_res_696_; 
v_sz_boxed_694_ = lean_unbox_usize(v_sz_691_);
lean_dec(v_sz_691_);
v_i_boxed_695_ = lean_unbox_usize(v_i_692_);
lean_dec(v_i_692_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_687_, v_sep_688_, v_afterSep_x3f_689_, v_afterElem_x3f_690_, v_sz_boxed_694_, v_i_boxed_695_, v_bs_693_);
lean_dec_ref(v_sepArray_687_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(lean_object* v_sep_697_, lean_object* v_sepArray_698_, lean_object* v_afterElem_x3f_699_, lean_object* v_afterSep_x3f_700_){
_start:
{
size_t v_sz_701_; size_t v___x_702_; lean_object* v_docs_703_; lean_object* v___x_704_; 
v_sz_701_ = lean_array_size(v_sepArray_698_);
v___x_702_ = ((size_t)0ULL);
lean_inc_ref(v_sepArray_698_);
v_docs_703_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_698_, v_sep_697_, v_afterSep_x3f_700_, v_afterElem_x3f_699_, v_sz_701_, v___x_702_, v_sepArray_698_);
lean_dec_ref(v_sepArray_698_);
v___x_704_ = l_Lean_Fmt_TaggedDoc_join(v_docs_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(lean_object* v_sepArray_705_, lean_object* v_sep_706_, lean_object* v_afterSep_x3f_707_, lean_object* v_afterElem_x3f_708_, lean_object* v_as_709_, size_t v_sz_710_, size_t v_i_711_, lean_object* v_bs_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_705_, v_sep_706_, v_afterSep_x3f_707_, v_afterElem_x3f_708_, v_sz_710_, v_i_711_, v_bs_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___boxed(lean_object* v_sepArray_714_, lean_object* v_sep_715_, lean_object* v_afterSep_x3f_716_, lean_object* v_afterElem_x3f_717_, lean_object* v_as_718_, lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_bs_721_){
_start:
{
size_t v_sz_boxed_722_; size_t v_i_boxed_723_; lean_object* v_res_724_; 
v_sz_boxed_722_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_723_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(v_sepArray_714_, v_sep_715_, v_afterSep_x3f_716_, v_afterElem_x3f_717_, v_as_718_, v_sz_boxed_722_, v_i_boxed_723_, v_bs_721_);
lean_dec_ref(v_as_718_);
lean_dec_ref(v_sepArray_714_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(lean_object* v_upperBound_725_, lean_object* v___x_726_, lean_object* v_sep_727_, lean_object* v_a_728_, lean_object* v_b_729_){
_start:
{
lean_object* v_a_731_; uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_lt(v_a_728_, v_upperBound_725_);
if (v___x_735_ == 0)
{
lean_dec(v_a_728_);
lean_dec_ref(v_sep_727_);
return v_b_729_;
}
else
{
lean_object* v_fst_736_; lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_757_; 
v_fst_736_ = lean_ctor_get(v_b_729_, 0);
v_snd_737_ = lean_ctor_get(v_b_729_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_b_729_);
if (v_isSharedCheck_757_ == 0)
{
v___x_739_ = v_b_729_;
v_isShared_740_ = v_isSharedCheck_757_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_inc(v_fst_736_);
lean_dec(v_b_729_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_757_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___y_742_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_array_fget_borrowed(v___x_726_, v_a_728_);
v___x_749_ = lean_unsigned_to_nat(2u);
v___x_750_ = lean_nat_mod(v_a_728_, v___x_749_);
v___x_751_ = lean_nat_dec_eq(v___x_750_, v___x_747_);
lean_dec(v___x_750_);
if (v___x_751_ == 0)
{
uint8_t v___x_752_; 
v___x_752_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_748_);
if (v___x_752_ == 0)
{
lean_inc(v___x_748_);
v___y_742_ = v___x_748_;
goto v___jp_741_;
}
else
{
if (v___x_751_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_inc_ref(v_sep_727_);
v___x_753_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_727_);
v___x_754_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_753_);
v___y_742_ = v___x_754_;
goto v___jp_741_;
}
else
{
lean_inc(v___x_748_);
v___y_742_ = v___x_748_;
goto v___jp_741_;
}
}
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_del_object(v___x_739_);
lean_inc(v___x_748_);
v___x_755_ = lean_array_push(v_fst_736_, v___x_748_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_snd_737_);
v_a_731_ = v___x_756_;
goto v___jp_730_;
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_array_push(v_snd_737_, v___y_742_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___x_743_);
v___x_745_ = v___x_739_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_fst_736_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
v_a_731_ = v___x_745_;
goto v___jp_730_;
}
}
}
}
v___jp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_a_728_, v___x_732_);
lean_dec(v_a_728_);
v_a_728_ = v___x_733_;
v_b_729_ = v_a_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg___boxed(lean_object* v_upperBound_758_, lean_object* v___x_759_, lean_object* v_sep_760_, lean_object* v_a_761_, lean_object* v_b_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_758_, v___x_759_, v_sep_760_, v_a_761_, v_b_762_);
lean_dec_ref(v___x_759_);
lean_dec(v_upperBound_758_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(lean_object* v_sep_766_, lean_object* v_sepArray_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_fst_772_; lean_object* v_snd_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_sepArray_767_);
v___x_770_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0));
v___x_771_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v___x_769_, v_sepArray_767_, v_sep_766_, v___x_768_, v___x_770_);
v_fst_772_ = lean_ctor_get(v___x_771_, 0);
v_snd_773_ = lean_ctor_get(v___x_771_, 1);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_771_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_snd_773_);
lean_inc(v_fst_772_);
lean_dec(v___x_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_fst_772_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_snd_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___boxed(lean_object* v_sep_781_, lean_object* v_sepArray_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_781_, v_sepArray_782_);
lean_dec_ref(v_sepArray_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(lean_object* v_upperBound_784_, lean_object* v___x_785_, lean_object* v_sep_786_, lean_object* v_inst_787_, lean_object* v_R_788_, lean_object* v_a_789_, lean_object* v_b_790_, lean_object* v_c_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_784_, v___x_785_, v_sep_786_, v_a_789_, v_b_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___boxed(lean_object* v_upperBound_793_, lean_object* v___x_794_, lean_object* v_sep_795_, lean_object* v_inst_796_, lean_object* v_R_797_, lean_object* v_a_798_, lean_object* v_b_799_, lean_object* v_c_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(v_upperBound_793_, v___x_794_, v_sep_795_, v_inst_796_, v_R_797_, v_a_798_, v_b_799_, v_c_800_);
lean_dec_ref(v___x_794_);
lean_dec(v_upperBound_793_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(lean_object* v_fst_802_, lean_object* v_val_803_, size_t v_sz_804_, size_t v_i_805_, lean_object* v_bs_806_){
_start:
{
uint8_t v___x_807_; 
v___x_807_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
if (v___x_807_ == 0)
{
lean_dec_ref(v_val_803_);
return v_bs_806_;
}
else
{
lean_object* v_v_808_; lean_object* v___x_809_; lean_object* v_bs_x27_810_; lean_object* v___y_812_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_v_808_ = lean_array_uget(v_bs_806_, v_i_805_);
v___x_809_ = lean_unsigned_to_nat(0u);
v_bs_x27_810_ = lean_array_uset(v_bs_806_, v_i_805_, v___x_809_);
v___x_817_ = lean_usize_to_nat(v_i_805_);
v___x_818_ = lean_array_get_size(v_fst_802_);
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_sub(v___x_818_, v___x_819_);
v___x_821_ = lean_nat_dec_eq(v___x_817_, v___x_820_);
lean_dec(v___x_820_);
lean_dec(v___x_817_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_inc_ref(v_val_803_);
v___x_822_ = l_Lean_Fmt_TaggedDoc_append(v_v_808_, v_val_803_);
v___y_812_ = v___x_822_;
goto v___jp_811_;
}
else
{
v___y_812_ = v_v_808_;
goto v___jp_811_;
}
v___jp_811_:
{
size_t v___x_813_; size_t v___x_814_; lean_object* v___x_815_; 
v___x_813_ = ((size_t)1ULL);
v___x_814_ = lean_usize_add(v_i_805_, v___x_813_);
v___x_815_ = lean_array_uset(v_bs_x27_810_, v_i_805_, v___y_812_);
v_i_805_ = v___x_814_;
v_bs_806_ = v___x_815_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg___boxed(lean_object* v_fst_823_, lean_object* v_val_824_, lean_object* v_sz_825_, lean_object* v_i_826_, lean_object* v_bs_827_){
_start:
{
size_t v_sz_boxed_828_; size_t v_i_boxed_829_; lean_object* v_res_830_; 
v_sz_boxed_828_ = lean_unbox_usize(v_sz_825_);
lean_dec(v_sz_825_);
v_i_boxed_829_ = lean_unbox_usize(v_i_826_);
lean_dec(v_i_826_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_823_, v_val_824_, v_sz_boxed_828_, v_i_boxed_829_, v_bs_827_);
lean_dec_ref(v_fst_823_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(lean_object* v_sep_831_, lean_object* v_sepArray_832_, lean_object* v_afterElem_x3f_833_){
_start:
{
lean_object* v_elems_835_; lean_object* v___x_838_; 
v___x_838_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_831_, v_sepArray_832_);
if (lean_obj_tag(v_afterElem_x3f_833_) == 1)
{
lean_object* v_fst_839_; lean_object* v_val_840_; size_t v_sz_841_; size_t v___x_842_; lean_object* v_elems_843_; 
v_fst_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc_n(v_fst_839_, 2);
lean_dec_ref(v___x_838_);
v_val_840_ = lean_ctor_get(v_afterElem_x3f_833_, 0);
lean_inc(v_val_840_);
lean_dec_ref_known(v_afterElem_x3f_833_, 1);
v_sz_841_ = lean_array_size(v_fst_839_);
v___x_842_ = ((size_t)0ULL);
v_elems_843_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_839_, v_val_840_, v_sz_841_, v___x_842_, v_fst_839_);
lean_dec(v_fst_839_);
v_elems_835_ = v_elems_843_;
goto v___jp_834_;
}
else
{
lean_object* v_fst_844_; 
lean_dec(v_afterElem_x3f_833_);
v_fst_844_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_fst_844_);
lean_dec_ref(v___x_838_);
v_elems_835_ = v_fst_844_;
goto v___jp_834_;
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_837_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_836_, v_elems_835_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl___boxed(lean_object* v_sep_845_, lean_object* v_sepArray_846_, lean_object* v_afterElem_x3f_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_845_, v_sepArray_846_, v_afterElem_x3f_847_);
lean_dec_ref(v_sepArray_846_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(lean_object* v_fst_849_, lean_object* v_val_850_, lean_object* v_as_851_, size_t v_sz_852_, size_t v_i_853_, lean_object* v_bs_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_849_, v_val_850_, v_sz_852_, v_i_853_, v_bs_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___boxed(lean_object* v_fst_856_, lean_object* v_val_857_, lean_object* v_as_858_, lean_object* v_sz_859_, lean_object* v_i_860_, lean_object* v_bs_861_){
_start:
{
size_t v_sz_boxed_862_; size_t v_i_boxed_863_; lean_object* v_res_864_; 
v_sz_boxed_862_ = lean_unbox_usize(v_sz_859_);
lean_dec(v_sz_859_);
v_i_boxed_863_ = lean_unbox_usize(v_i_860_);
lean_dec(v_i_860_);
v_res_864_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(v_fst_856_, v_val_857_, v_as_858_, v_sz_boxed_862_, v_i_boxed_863_, v_bs_861_);
lean_dec_ref(v_as_858_);
lean_dec_ref(v_fst_856_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0___redArg(lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v_a_867_, lean_object* v_b_868_){
_start:
{
lean_object* v_array_869_; lean_object* v_start_870_; lean_object* v_stop_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_954_; 
v_array_869_ = lean_ctor_get(v_a_867_, 0);
v_start_870_ = lean_ctor_get(v_a_867_, 1);
v_stop_871_ = lean_ctor_get(v_a_867_, 2);
v_isSharedCheck_954_ = !lean_is_exclusive(v_a_867_);
if (v_isSharedCheck_954_ == 0)
{
v___x_873_ = v_a_867_;
v_isShared_874_ = v_isSharedCheck_954_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_stop_871_);
lean_inc(v_start_870_);
lean_inc(v_array_869_);
lean_dec(v_a_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_954_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = lean_nat_dec_lt(v_start_870_, v_stop_871_);
if (v___x_875_ == 0)
{
lean_del_object(v___x_873_);
lean_dec(v_stop_871_);
lean_dec(v_start_870_);
lean_dec_ref(v_array_869_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v___y_865_);
return v_b_868_;
}
else
{
lean_object* v_snd_876_; lean_object* v_snd_877_; lean_object* v_fst_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_952_; 
v_snd_876_ = lean_ctor_get(v_b_868_, 1);
lean_inc(v_snd_876_);
v_snd_877_ = lean_ctor_get(v_snd_876_, 1);
lean_inc(v_snd_877_);
v_fst_878_ = lean_ctor_get(v_b_868_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v_b_868_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v_b_868_, 1);
lean_dec(v_unused_953_);
v___x_880_ = v_b_868_;
v_isShared_881_ = v_isSharedCheck_952_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_fst_878_);
lean_dec(v_b_868_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_952_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_fst_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_950_; 
v_fst_882_ = lean_ctor_get(v_snd_876_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_snd_876_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_snd_876_, 1);
lean_dec(v_unused_951_);
v___x_884_ = v_snd_876_;
v_isShared_885_ = v_isSharedCheck_950_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_fst_882_);
lean_dec(v_snd_876_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_950_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_array_886_; lean_object* v_start_887_; lean_object* v_stop_888_; uint8_t v___x_889_; 
v_array_886_ = lean_ctor_get(v_snd_877_, 0);
v_start_887_ = lean_ctor_get(v_snd_877_, 1);
v_stop_888_ = lean_ctor_get(v_snd_877_, 2);
v___x_889_ = lean_nat_dec_lt(v_start_887_, v_stop_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_891_; 
lean_del_object(v___x_873_);
lean_dec(v_stop_871_);
lean_dec(v_start_870_);
lean_dec_ref(v_array_869_);
lean_dec_ref(v___y_866_);
lean_dec_ref(v___y_865_);
if (v_isShared_885_ == 0)
{
v___x_891_ = v___x_884_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_fst_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_snd_877_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_891_);
v___x_893_ = v___x_880_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_fst_878_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_946_; 
lean_inc(v_stop_888_);
lean_inc(v_start_887_);
lean_inc_ref(v_array_886_);
v_isSharedCheck_946_ = !lean_is_exclusive(v_snd_877_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; lean_object* v_unused_948_; lean_object* v_unused_949_; 
v_unused_947_ = lean_ctor_get(v_snd_877_, 2);
lean_dec(v_unused_947_);
v_unused_948_ = lean_ctor_get(v_snd_877_, 1);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_snd_877_, 0);
lean_dec(v_unused_949_);
v___x_897_ = v_snd_877_;
v_isShared_898_ = v_isSharedCheck_946_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_snd_877_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_946_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_902_; 
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_add(v_start_870_, v___x_899_);
lean_inc_ref(v_array_869_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 2, v_stop_871_);
lean_ctor_set(v___x_897_, 1, v___x_900_);
lean_ctor_set(v___x_897_, 0, v_array_869_);
v___x_902_ = v___x_897_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_array_869_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_stop_871_);
v___x_902_ = v_reuseFailAlloc_945_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_903_ = lean_array_fget(v_array_869_, v_start_870_);
lean_dec(v_start_870_);
lean_dec_ref(v_array_869_);
v___x_904_ = lean_array_fget(v_array_886_, v_start_887_);
v___x_905_ = lean_nat_add(v_start_887_, v___x_899_);
lean_dec(v_start_887_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 2, v_stop_888_);
lean_ctor_set(v___x_873_, 1, v___x_905_);
lean_ctor_set(v___x_873_, 0, v_array_886_);
v___x_907_ = v___x_873_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_array_886_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_stop_888_);
v___x_907_ = v_reuseFailAlloc_944_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_908_ = lean_unsigned_to_nat(2u);
v___x_909_ = lean_mk_empty_array_with_capacity(v___x_908_);
lean_inc(v_fst_878_);
lean_inc_ref(v___x_909_);
v___x_910_ = lean_array_push(v___x_909_, v_fst_878_);
v___x_911_ = lean_array_push(v___x_910_, v_fst_882_);
v___x_912_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_911_);
lean_inc(v___x_903_);
v___x_913_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_903_);
v___x_914_ = lean_unsigned_to_nat(5u);
v___x_915_ = lean_mk_empty_array_with_capacity(v___x_914_);
v___x_916_ = lean_array_push(v___x_915_, v_fst_878_);
lean_inc_ref_n(v___y_865_, 2);
v___x_917_ = lean_array_push(v___x_916_, v___y_865_);
lean_inc(v___x_904_);
v___x_918_ = lean_array_push(v___x_917_, v___x_904_);
lean_inc_ref_n(v___y_866_, 2);
v___x_919_ = lean_array_push(v___x_918_, v___y_866_);
lean_inc_ref(v___x_913_);
v___x_920_ = lean_array_push(v___x_919_, v___x_913_);
v___x_921_ = l_Lean_Fmt_TaggedDoc_join(v___x_920_);
v___x_922_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_923_ = lean_unsigned_to_nat(6u);
v___x_924_ = lean_mk_empty_array_with_capacity(v___x_923_);
v___x_925_ = lean_array_push(v___x_924_, v___x_912_);
v___x_926_ = lean_array_push(v___x_925_, v___y_865_);
v___x_927_ = lean_array_push(v___x_926_, v___x_904_);
v___x_928_ = lean_array_push(v___x_927_, v___y_866_);
v___x_929_ = lean_array_push(v___x_928_, v___x_922_);
lean_inc_ref(v___x_929_);
v___x_930_ = lean_array_push(v___x_929_, v___x_913_);
v___x_931_ = l_Lean_Fmt_TaggedDoc_join(v___x_930_);
v___x_932_ = lean_array_push(v___x_909_, v___x_921_);
v___x_933_ = lean_array_push(v___x_932_, v___x_931_);
v___x_934_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_933_);
v___x_935_ = lean_array_push(v___x_929_, v___x_903_);
v___x_936_ = l_Lean_Fmt_TaggedDoc_join(v___x_935_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_907_);
lean_ctor_set(v___x_884_, 0, v___x_936_);
v___x_938_ = v___x_884_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_907_);
v___x_938_ = v_reuseFailAlloc_943_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___x_938_);
lean_ctor_set(v___x_880_, 0, v___x_934_);
v___x_940_ = v___x_880_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_942_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
v_a_867_ = v___x_902_;
v_b_868_ = v___x_940_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(lean_object* v_sep_955_, lean_object* v_sepArray_956_, lean_object* v_afterElem_x3f_957_, lean_object* v_afterSep_x3f_958_){
_start:
{
lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v_elems_963_; lean_object* v_seps_964_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_1021_; 
if (lean_obj_tag(v_afterElem_x3f_957_) == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1021_ = v___x_1024_;
goto v___jp_1020_;
}
else
{
lean_object* v_val_1025_; 
v_val_1025_ = lean_ctor_get(v_afterElem_x3f_957_, 0);
lean_inc(v_val_1025_);
lean_dec_ref_known(v_afterElem_x3f_957_, 1);
v___y_1021_ = v_val_1025_;
goto v___jp_1020_;
}
v___jp_959_:
{
lean_object* v___x_965_; lean_object* v_lastNotFlattened_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_965_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_lastNotFlattened_966_ = lean_array_get(v___x_965_, v_elems_963_, v___y_961_);
v___x_967_ = lean_array_get_size(v_elems_963_);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_dec_eq(v___x_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v_lastFlattened_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_snd_977_; lean_object* v_fst_978_; lean_object* v_fst_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_inc(v_lastNotFlattened_966_);
v_lastFlattened_970_ = l_Lean_Fmt_TaggedDoc_flattened(v_lastNotFlattened_966_);
v___x_971_ = lean_array_get_size(v_seps_964_);
v___x_972_ = l_Array_toSubarray___redArg(v_seps_964_, v___y_961_, v___x_971_);
v___x_973_ = l_Array_toSubarray___redArg(v_elems_963_, v___x_968_, v___x_967_);
v___x_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_974_, 0, v_lastNotFlattened_966_);
lean_ctor_set(v___x_974_, 1, v___x_972_);
v___x_975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_975_, 0, v_lastFlattened_970_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0___redArg(v___y_962_, v___y_960_, v___x_973_, v___x_975_);
v_snd_977_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_snd_977_);
v_fst_978_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_fst_978_);
lean_dec_ref(v___x_976_);
v_fst_979_ = lean_ctor_get(v_snd_977_, 0);
lean_inc(v_fst_979_);
lean_dec(v_snd_977_);
v___x_980_ = lean_unsigned_to_nat(2u);
v___x_981_ = lean_mk_empty_array_with_capacity(v___x_980_);
v___x_982_ = lean_array_push(v___x_981_, v_fst_978_);
v___x_983_ = lean_array_push(v___x_982_, v_fst_979_);
v___x_984_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_983_);
return v___x_984_;
}
else
{
lean_dec_ref(v_seps_964_);
lean_dec_ref(v_elems_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_lastNotFlattened_966_;
}
}
v___jp_985_:
{
lean_object* v_seps_991_; 
v_seps_991_ = lean_array_pop(v___y_988_);
v___y_960_ = v___y_986_;
v___y_961_ = v___y_987_;
v___y_962_ = v___y_989_;
v_elems_963_ = v___y_990_;
v_seps_964_ = v_seps_991_;
goto v___jp_959_;
}
v___jp_992_:
{
lean_object* v___x_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_995_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_955_, v_sepArray_956_);
v_fst_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_fst_996_);
v_snd_997_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_snd_997_);
lean_dec_ref(v___x_995_);
v___x_998_ = lean_array_get_size(v_fst_996_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_nat_dec_eq(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_array_get_size(v_snd_997_);
v___x_1002_ = lean_nat_dec_eq(v___x_1001_, v___x_998_);
if (v___x_1002_ == 0)
{
v___y_960_ = v___y_994_;
v___y_961_ = v___x_999_;
v___y_962_ = v___y_993_;
v_elems_963_ = v_fst_996_;
v_seps_964_ = v_snd_997_;
goto v___jp_959_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_sub(v___x_998_, v___x_1003_);
v___x_1005_ = lean_nat_dec_lt(v___x_1004_, v___x_998_);
if (v___x_1005_ == 0)
{
lean_dec(v___x_1004_);
v___y_986_ = v___y_994_;
v___y_987_ = v___x_999_;
v___y_988_ = v_snd_997_;
v___y_989_ = v___y_993_;
v___y_990_ = v_fst_996_;
goto v___jp_985_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_trailingSep_1008_; lean_object* v_v_1009_; lean_object* v___x_1010_; lean_object* v_xs_x27_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1006_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1007_ = lean_nat_sub(v___x_1001_, v___x_1003_);
v_trailingSep_1008_ = lean_array_get_borrowed(v___x_1006_, v_snd_997_, v___x_1007_);
lean_dec(v___x_1007_);
v_v_1009_ = lean_array_fget(v_fst_996_, v___x_1004_);
v___x_1010_ = lean_box(0);
v_xs_x27_1011_ = lean_array_fset(v_fst_996_, v___x_1004_, v___x_1010_);
v___x_1012_ = lean_unsigned_to_nat(3u);
v___x_1013_ = lean_mk_empty_array_with_capacity(v___x_1012_);
v___x_1014_ = lean_array_push(v___x_1013_, v_v_1009_);
lean_inc_ref(v___y_993_);
v___x_1015_ = lean_array_push(v___x_1014_, v___y_993_);
lean_inc(v_trailingSep_1008_);
v___x_1016_ = lean_array_push(v___x_1015_, v_trailingSep_1008_);
v___x_1017_ = l_Lean_Fmt_TaggedDoc_join(v___x_1016_);
v___x_1018_ = lean_array_fset(v_xs_x27_1011_, v___x_1004_, v___x_1017_);
lean_dec(v___x_1004_);
v___y_986_ = v___y_994_;
v___y_987_ = v___x_999_;
v___y_988_ = v_snd_997_;
v___y_989_ = v___y_993_;
v___y_990_ = v___x_1018_;
goto v___jp_985_;
}
}
}
else
{
lean_object* v___x_1019_; 
lean_dec(v_snd_997_);
lean_dec(v_fst_996_);
lean_dec_ref(v___y_994_);
lean_dec_ref(v___y_993_);
v___x_1019_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1019_;
}
}
v___jp_1020_:
{
if (lean_obj_tag(v_afterSep_x3f_958_) == 0)
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_993_ = v___y_1021_;
v___y_994_ = v___x_1022_;
goto v___jp_992_;
}
else
{
lean_object* v_val_1023_; 
v_val_1023_ = lean_ctor_get(v_afterSep_x3f_958_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v_afterSep_x3f_958_, 1);
v___y_993_ = v___y_1021_;
v___y_994_ = v_val_1023_;
goto v___jp_992_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___boxed(lean_object* v_sep_1026_, lean_object* v_sepArray_1027_, lean_object* v_afterElem_x3f_1028_, lean_object* v_afterSep_x3f_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_1026_, v_sepArray_1027_, v_afterElem_x3f_1028_, v_afterSep_x3f_1029_);
lean_dec_ref(v_sepArray_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0(lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v_inst_1033_, lean_object* v_R_1034_, lean_object* v_a_1035_, lean_object* v_b_1036_, lean_object* v_c_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0___redArg(v___y_1031_, v___y_1032_, v_a_1035_, v_b_1036_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepArray___closed__0(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = l_Lean_Fmt_TaggedDoc_space;
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object* v_sep_1041_, lean_object* v_sepArray_1042_, lean_object* v_format_1043_){
_start:
{
uint8_t v___y_1045_; 
if (lean_obj_tag(v_format_1043_) == 1)
{
uint8_t v_trailingSep_1072_; 
v_trailingSep_1072_ = lean_ctor_get_uint8(v_format_1043_, sizeof(void*)*1 + 1);
v___y_1045_ = v_trailingSep_1072_;
goto v___jp_1044_;
}
else
{
uint8_t v_trailingSep_1073_; 
v_trailingSep_1073_ = lean_ctor_get_uint8(v_format_1043_, sizeof(void*)*2);
v___y_1045_ = v_trailingSep_1073_;
goto v___jp_1044_;
}
v___jp_1044_:
{
lean_object* v_sepArray_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
lean_inc_ref(v_sep_1041_);
v_sepArray_1046_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1041_, v_sepArray_1042_, v___y_1045_);
v___x_1047_ = lean_array_get_size(v_sepArray_1046_);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_nat_dec_eq(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_nat_dec_eq(v___x_1047_, v___x_1050_);
if (v___x_1051_ == 0)
{
switch(lean_obj_tag(v_format_1043_))
{
case 0:
{
lean_object* v_afterElem_x3f_1052_; lean_object* v_afterSep_x3f_1053_; lean_object* v___x_1054_; 
v_afterElem_x3f_1052_ = lean_ctor_get(v_format_1043_, 0);
lean_inc(v_afterElem_x3f_1052_);
v_afterSep_x3f_1053_ = lean_ctor_get(v_format_1043_, 1);
lean_inc(v_afterSep_x3f_1053_);
lean_dec_ref_known(v_format_1043_, 2);
v___x_1054_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1041_, v_sepArray_1046_, v_afterElem_x3f_1052_, v_afterSep_x3f_1053_);
return v___x_1054_;
}
case 1:
{
uint8_t v_allowFlattening_1055_; lean_object* v_afterElem_x3f_1056_; lean_object* v_joinedUsingNl_1057_; 
v_allowFlattening_1055_ = lean_ctor_get_uint8(v_format_1043_, sizeof(void*)*1);
v_afterElem_x3f_1056_ = lean_ctor_get(v_format_1043_, 0);
lean_inc_n(v_afterElem_x3f_1056_, 2);
lean_dec_ref_known(v_format_1043_, 1);
lean_inc_ref(v_sep_1041_);
v_joinedUsingNl_1057_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_1041_, v_sepArray_1046_, v_afterElem_x3f_1056_);
if (v_allowFlattening_1055_ == 0)
{
lean_dec(v_afterElem_x3f_1056_);
lean_dec_ref(v_sepArray_1046_);
lean_dec_ref(v_sep_1041_);
return v_joinedUsingNl_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1058_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepArray___closed__0, &l_Lean_Fmt_Layouts_sepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_sepArray___closed__0);
v___x_1059_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1041_, v_sepArray_1046_, v_afterElem_x3f_1056_, v___x_1058_);
v___x_1060_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1059_);
v___x_1061_ = lean_unsigned_to_nat(2u);
v___x_1062_ = lean_mk_empty_array_with_capacity(v___x_1061_);
v___x_1063_ = lean_array_push(v___x_1062_, v___x_1060_);
v___x_1064_ = lean_array_push(v___x_1063_, v_joinedUsingNl_1057_);
v___x_1065_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1064_);
return v___x_1065_;
}
}
default: 
{
lean_object* v_afterElem_x3f_1066_; lean_object* v_afterSep_x3f_1067_; lean_object* v___x_1068_; 
v_afterElem_x3f_1066_ = lean_ctor_get(v_format_1043_, 0);
lean_inc(v_afterElem_x3f_1066_);
v_afterSep_x3f_1067_ = lean_ctor_get(v_format_1043_, 1);
lean_inc(v_afterSep_x3f_1067_);
lean_dec_ref_known(v_format_1043_, 2);
v___x_1068_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_1041_, v_sepArray_1046_, v_afterElem_x3f_1066_, v_afterSep_x3f_1067_);
lean_dec_ref(v_sepArray_1046_);
return v___x_1068_;
}
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec_ref(v_format_1043_);
lean_dec_ref(v_sep_1041_);
v___x_1069_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1070_ = lean_array_get(v___x_1069_, v_sepArray_1046_, v___x_1048_);
lean_dec_ref(v_sepArray_1046_);
return v___x_1070_;
}
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_sepArray_1046_);
lean_dec_ref(v_format_1043_);
lean_dec_ref(v_sep_1041_);
v___x_1071_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1071_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray___boxed(lean_object* v_sep_1074_, lean_object* v_sepArray_1075_, lean_object* v_format_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1074_, v_sepArray_1075_, v_format_1076_);
lean_dec_ref(v_sepArray_1075_);
return v_res_1077_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__0(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__1(void){
_start:
{
uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1080_ = 1;
v___x_1081_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__0, &l_Lean_Fmt_Layouts_sepLines___closed__0_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__0);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*2, v___x_1080_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object* v_sep_1084_, lean_object* v_lines_1085_, uint8_t v_includeSeps_1086_){
_start:
{
if (v_includeSeps_1086_ == 0)
{
lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = 1;
v___x_1089_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*1, v_includeSeps_1086_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*1 + 1, v___x_1088_);
v___x_1090_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1084_, v_lines_1085_, v___x_1089_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__1, &l_Lean_Fmt_Layouts_sepLines___closed__1_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__1);
v___x_1092_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1084_, v_lines_1085_, v___x_1091_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines___boxed(lean_object* v_sep_1093_, lean_object* v_lines_1094_, lean_object* v_includeSeps_1095_){
_start:
{
uint8_t v_includeSeps_boxed_1096_; lean_object* v_res_1097_; 
v_includeSeps_boxed_1096_ = lean_unbox(v_includeSeps_1095_);
v_res_1097_ = l_Lean_Fmt_Layouts_sepLines(v_sep_1093_, v_lines_1094_, v_includeSeps_boxed_1096_);
lean_dec_ref(v_lines_1094_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepFill___closed__0(void){
_start:
{
uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1098_ = 1;
v___x_1099_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepArray___closed__0, &l_Lean_Fmt_Layouts_sepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_sepArray___closed__0);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_alloc_ctor(2, 2, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v___x_1099_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*2, v___x_1098_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object* v_sep_1102_, lean_object* v_elems_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepFill___closed__0, &l_Lean_Fmt_Layouts_sepFill___closed__0_once, _init_l_Lean_Fmt_Layouts_sepFill___closed__0);
v___x_1105_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1102_, v_elems_1103_, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill___boxed(lean_object* v_sep_1106_, lean_object* v_elems_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_Fmt_Layouts_sepFill(v_sep_1106_, v_elems_1107_);
lean_dec_ref(v_elems_1107_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2(void){
_start:
{
uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = 1;
v___x_1116_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1);
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v___x_1116_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*2, v___x_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical(lean_object* v_sep_1119_, lean_object* v_elems_1120_, uint8_t v_includeSeps_1121_){
_start:
{
uint8_t v___x_1122_; lean_object* v_elems_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1122_ = 1;
lean_inc_ref(v_sep_1119_);
v_elems_1123_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1119_, v_elems_1120_, v___x_1122_);
v___x_1124_ = lean_array_get_size(v_elems_1123_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_dec_eq(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
if (v_includeSeps_1121_ == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = ((lean_object*)(l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0));
v___x_1128_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1119_, v_elems_1123_, v___x_1127_);
lean_dec_ref(v_elems_1123_);
return v___x_1128_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v___x_1130_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1119_, v_elems_1123_, v___x_1129_);
lean_dec_ref(v_elems_1123_);
v___x_1131_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_1130_);
return v___x_1131_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_sep_1119_);
v___x_1132_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_array_get(v___x_1132_, v_elems_1123_, v___x_1133_);
lean_dec_ref(v_elems_1123_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___boxed(lean_object* v_sep_1135_, lean_object* v_elems_1136_, lean_object* v_includeSeps_1137_){
_start:
{
uint8_t v_includeSeps_boxed_1138_; lean_object* v_res_1139_; 
v_includeSeps_boxed_1138_ = lean_unbox(v_includeSeps_1137_);
v_res_1139_ = l_Lean_Fmt_Layouts_sepHorizontalOrVertical(v_sep_1135_, v_elems_1136_, v_includeSeps_boxed_1138_);
lean_dec_ref(v_elems_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(lean_object* v___x_1140_, lean_object* v_docsWithIntermediateWhitespace_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_fst_1143_; lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1173_; 
v_fst_1143_ = lean_ctor_get(v_a_1142_, 0);
v_snd_1144_ = lean_ctor_get(v_a_1142_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_a_1142_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1146_ = v_a_1142_;
v_isShared_1147_ = v_isSharedCheck_1173_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_inc(v_fst_1143_);
lean_dec(v_a_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1173_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_nat_dec_lt(v_snd_1144_, v___x_1140_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1150_; 
if (v_isShared_1147_ == 0)
{
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_fst_1143_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_snd_1144_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
else
{
lean_object* v___f_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___y_1157_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___f_1152_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1155_ = lean_array_get_borrowed(v___x_1154_, v_docsWithIntermediateWhitespace_1141_, v_snd_1144_);
v___x_1168_ = lean_nat_add(v_snd_1144_, v___x_1153_);
v___x_1169_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1141_);
v___x_1170_ = lean_nat_dec_lt(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec(v___x_1168_);
v___x_1171_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1157_ = v___x_1171_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_array_fget_borrowed(v_docsWithIntermediateWhitespace_1141_, v___x_1168_);
lean_dec(v___x_1168_);
lean_inc(v___x_1172_);
v___y_1157_ = v___x_1172_;
goto v___jp_1156_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_inc(v___x_1155_);
v___x_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___y_1157_);
lean_ctor_set(v___x_1159_, 1, v___f_1152_);
v___x_1160_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1158_, v___x_1159_);
v___x_1161_ = lean_array_push(v_fst_1143_, v___x_1160_);
v___x_1162_ = lean_unsigned_to_nat(2u);
v___x_1163_ = lean_nat_add(v_snd_1144_, v___x_1162_);
lean_dec(v_snd_1144_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v___x_1163_);
lean_ctor_set(v___x_1146_, 0, v___x_1161_);
v___x_1165_ = v___x_1146_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
v_a_1142_ = v___x_1165_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg___boxed(lean_object* v___x_1174_, lean_object* v_docsWithIntermediateWhitespace_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1174_, v_docsWithIntermediateWhitespace_1175_, v_a_1176_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1175_);
lean_dec(v___x_1174_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object* v_docsWithIntermediateWhitespace_1183_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1184_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1183_);
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_nat_dec_eq(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_dec_eq(v___x_1184_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_fst_1191_; lean_object* v___x_1192_; 
v___x_1189_ = ((lean_object*)(l_Lean_Fmt_Layouts_retainedWhitespace___closed__1));
v___x_1190_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1184_, v_docsWithIntermediateWhitespace_1183_, v___x_1189_);
v_fst_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_fst_1191_);
lean_dec_ref(v___x_1190_);
v___x_1192_ = l_Lean_Fmt_TaggedDoc_combine(v_fst_1191_);
lean_dec(v_fst_1191_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1194_ = lean_array_get_borrowed(v___x_1193_, v_docsWithIntermediateWhitespace_1183_, v___x_1185_);
lean_inc(v___x_1194_);
return v___x_1194_;
}
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___boxed(lean_object* v_docsWithIntermediateWhitespace_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Fmt_Layouts_retainedWhitespace(v_docsWithIntermediateWhitespace_1196_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(lean_object* v___x_1198_, lean_object* v_docsWithIntermediateWhitespace_1199_, lean_object* v_inst_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1198_, v_docsWithIntermediateWhitespace_1199_, v_a_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___boxed(lean_object* v___x_1203_, lean_object* v_docsWithIntermediateWhitespace_1204_, lean_object* v_inst_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(v___x_1203_, v_docsWithIntermediateWhitespace_1204_, v_inst_1205_, v_a_1206_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1204_);
lean_dec(v___x_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1___redArg(lean_object* v_v_1208_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1(lean_object* v_00_u03c4_1210_, lean_object* v_v_1211_){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(lean_object* v_a_1213_, lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = lean_box(0);
return v___x_1215_;
}
else
{
lean_object* v_key_1216_; lean_object* v_value_1217_; lean_object* v_tail_1218_; size_t v_ptr_1219_; size_t v_ptr_1220_; uint8_t v___x_1221_; 
v_key_1216_ = lean_ctor_get(v_x_1214_, 0);
v_value_1217_ = lean_ctor_get(v_x_1214_, 1);
v_tail_1218_ = lean_ctor_get(v_x_1214_, 2);
v_ptr_1219_ = lean_ctor_get_usize(v_key_1216_, 1);
v_ptr_1220_ = lean_ctor_get_usize(v_a_1213_, 1);
v___x_1221_ = lean_usize_dec_eq(v_ptr_1219_, v_ptr_1220_);
if (v___x_1221_ == 0)
{
v_x_1214_ = v_tail_1218_;
goto _start;
}
else
{
lean_object* v___x_1223_; 
lean_inc(v_value_1217_);
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_value_1217_);
return v___x_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg___boxed(lean_object* v_a_1224_, lean_object* v_x_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1224_, v_x_1225_);
lean_dec(v_x_1225_);
lean_dec_ref(v_a_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(lean_object* v_m_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v_buckets_1229_; size_t v_ptr_1230_; lean_object* v___x_1231_; uint64_t v___x_1232_; uint64_t v___x_1233_; uint64_t v___x_1234_; uint64_t v_fold_1235_; uint64_t v___x_1236_; uint64_t v___x_1237_; uint64_t v___x_1238_; size_t v___x_1239_; size_t v___x_1240_; size_t v___x_1241_; size_t v___x_1242_; size_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_buckets_1229_ = lean_ctor_get(v_m_1227_, 1);
v_ptr_1230_ = lean_ctor_get_usize(v_a_1228_, 1);
v___x_1231_ = lean_array_get_size(v_buckets_1229_);
v___x_1232_ = lean_usize_to_uint64(v_ptr_1230_);
v___x_1233_ = 32ULL;
v___x_1234_ = lean_uint64_shift_right(v___x_1232_, v___x_1233_);
v_fold_1235_ = lean_uint64_xor(v___x_1232_, v___x_1234_);
v___x_1236_ = 16ULL;
v___x_1237_ = lean_uint64_shift_right(v_fold_1235_, v___x_1236_);
v___x_1238_ = lean_uint64_xor(v_fold_1235_, v___x_1237_);
v___x_1239_ = lean_uint64_to_usize(v___x_1238_);
v___x_1240_ = lean_usize_of_nat(v___x_1231_);
v___x_1241_ = ((size_t)1ULL);
v___x_1242_ = lean_usize_sub(v___x_1240_, v___x_1241_);
v___x_1243_ = lean_usize_land(v___x_1239_, v___x_1242_);
v___x_1244_ = lean_array_uget_borrowed(v_buckets_1229_, v___x_1243_);
v___x_1245_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1228_, v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg___boxed(lean_object* v_m_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1246_, v_a_1247_);
lean_dec_ref(v_a_1247_);
lean_dec_ref(v_m_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(lean_object* v_a_1249_, lean_object* v_b_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
lean_dec(v_b_1250_);
lean_dec_ref(v_a_1249_);
return v_x_1251_;
}
else
{
lean_object* v_key_1252_; lean_object* v_value_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1268_; 
v_key_1252_ = lean_ctor_get(v_x_1251_, 0);
v_value_1253_ = lean_ctor_get(v_x_1251_, 1);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 2);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1256_ = v_x_1251_;
v_isShared_1257_ = v_isSharedCheck_1268_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_value_1253_);
lean_inc(v_key_1252_);
lean_dec(v_x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1268_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
size_t v_ptr_1258_; size_t v_ptr_1259_; uint8_t v___x_1260_; 
v_ptr_1258_ = lean_ctor_get_usize(v_key_1252_, 1);
v_ptr_1259_ = lean_ctor_get_usize(v_a_1249_, 1);
v___x_1260_ = lean_usize_dec_eq(v_ptr_1258_, v_ptr_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1249_, v_b_1250_, v_tail_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 2, v___x_1261_);
v___x_1263_ = v___x_1256_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_key_1252_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_value_1253_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
else
{
lean_object* v___x_1266_; 
lean_dec(v_value_1253_);
lean_dec(v_key_1252_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_b_1250_);
lean_ctor_set(v___x_1256_, 0, v_a_1249_);
v___x_1266_ = v___x_1256_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1249_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_b_1250_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_tail_1254_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
return v_x_1269_;
}
else
{
lean_object* v_key_1271_; lean_object* v_value_1272_; lean_object* v_tail_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1297_; 
v_key_1271_ = lean_ctor_get(v_x_1270_, 0);
v_value_1272_ = lean_ctor_get(v_x_1270_, 1);
v_tail_1273_ = lean_ctor_get(v_x_1270_, 2);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_x_1270_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1275_ = v_x_1270_;
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_tail_1273_);
lean_inc(v_value_1272_);
lean_inc(v_key_1271_);
lean_dec(v_x_1270_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
size_t v_ptr_1277_; lean_object* v___x_1278_; uint64_t v___x_1279_; uint64_t v___x_1280_; uint64_t v___x_1281_; uint64_t v_fold_1282_; uint64_t v___x_1283_; uint64_t v___x_1284_; uint64_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v_ptr_1277_ = lean_ctor_get_usize(v_key_1271_, 1);
v___x_1278_ = lean_array_get_size(v_x_1269_);
v___x_1279_ = lean_usize_to_uint64(v_ptr_1277_);
v___x_1280_ = 32ULL;
v___x_1281_ = lean_uint64_shift_right(v___x_1279_, v___x_1280_);
v_fold_1282_ = lean_uint64_xor(v___x_1279_, v___x_1281_);
v___x_1283_ = 16ULL;
v___x_1284_ = lean_uint64_shift_right(v_fold_1282_, v___x_1283_);
v___x_1285_ = lean_uint64_xor(v_fold_1282_, v___x_1284_);
v___x_1286_ = lean_uint64_to_usize(v___x_1285_);
v___x_1287_ = lean_usize_of_nat(v___x_1278_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_sub(v___x_1287_, v___x_1288_);
v___x_1290_ = lean_usize_land(v___x_1286_, v___x_1289_);
v___x_1291_ = lean_array_uget_borrowed(v_x_1269_, v___x_1290_);
lean_inc(v___x_1291_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 2, v___x_1291_);
v___x_1293_ = v___x_1275_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_key_1271_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_value_1272_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_array_uset(v_x_1269_, v___x_1290_, v___x_1293_);
v_x_1269_ = v___x_1294_;
v_x_1270_ = v_tail_1273_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(lean_object* v_i_1298_, lean_object* v_source_1299_, lean_object* v_target_1300_){
_start:
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_array_get_size(v_source_1299_);
v___x_1302_ = lean_nat_dec_lt(v_i_1298_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v_source_1299_);
lean_dec(v_i_1298_);
return v_target_1300_;
}
else
{
lean_object* v_es_1303_; lean_object* v___x_1304_; lean_object* v_source_1305_; lean_object* v_target_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v_es_1303_ = lean_array_fget(v_source_1299_, v_i_1298_);
v___x_1304_ = lean_box(0);
v_source_1305_ = lean_array_fset(v_source_1299_, v_i_1298_, v___x_1304_);
v_target_1306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_target_1300_, v_es_1303_);
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_nat_add(v_i_1298_, v___x_1307_);
lean_dec(v_i_1298_);
v_i_1298_ = v___x_1308_;
v_source_1299_ = v_source_1305_;
v_target_1300_ = v_target_1306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(lean_object* v_data_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_nbuckets_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1311_ = lean_array_get_size(v_data_1310_);
v___x_1312_ = lean_unsigned_to_nat(2u);
v_nbuckets_1313_ = lean_nat_mul(v___x_1311_, v___x_1312_);
v___x_1314_ = lean_unsigned_to_nat(0u);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_mk_array(v_nbuckets_1313_, v___x_1315_);
v___x_1317_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v___x_1314_, v_data_1310_, v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(lean_object* v_a_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 0)
{
uint8_t v___x_1320_; 
v___x_1320_ = 0;
return v___x_1320_;
}
else
{
lean_object* v_key_1321_; lean_object* v_tail_1322_; size_t v_ptr_1323_; size_t v_ptr_1324_; uint8_t v___x_1325_; 
v_key_1321_ = lean_ctor_get(v_x_1319_, 0);
v_tail_1322_ = lean_ctor_get(v_x_1319_, 2);
v_ptr_1323_ = lean_ctor_get_usize(v_key_1321_, 1);
v_ptr_1324_ = lean_ctor_get_usize(v_a_1318_, 1);
v___x_1325_ = lean_usize_dec_eq(v_ptr_1323_, v_ptr_1324_);
if (v___x_1325_ == 0)
{
v_x_1319_ = v_tail_1322_;
goto _start;
}
else
{
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg___boxed(lean_object* v_a_1327_, lean_object* v_x_1328_){
_start:
{
uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_res_1329_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1327_, v_x_1328_);
lean_dec(v_x_1328_);
lean_dec_ref(v_a_1327_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(lean_object* v_m_1331_, lean_object* v_a_1332_, lean_object* v_b_1333_){
_start:
{
lean_object* v_size_1334_; lean_object* v_buckets_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1379_; 
v_size_1334_ = lean_ctor_get(v_m_1331_, 0);
v_buckets_1335_ = lean_ctor_get(v_m_1331_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_m_1331_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1337_ = v_m_1331_;
v_isShared_1338_ = v_isSharedCheck_1379_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_buckets_1335_);
lean_inc(v_size_1334_);
lean_dec(v_m_1331_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1379_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
size_t v_ptr_1339_; lean_object* v___x_1340_; uint64_t v___x_1341_; uint64_t v___x_1342_; uint64_t v___x_1343_; uint64_t v_fold_1344_; uint64_t v___x_1345_; uint64_t v___x_1346_; uint64_t v___x_1347_; size_t v___x_1348_; size_t v___x_1349_; size_t v___x_1350_; size_t v___x_1351_; size_t v___x_1352_; lean_object* v_bkt_1353_; uint8_t v___x_1354_; 
v_ptr_1339_ = lean_ctor_get_usize(v_a_1332_, 1);
v___x_1340_ = lean_array_get_size(v_buckets_1335_);
v___x_1341_ = lean_usize_to_uint64(v_ptr_1339_);
v___x_1342_ = 32ULL;
v___x_1343_ = lean_uint64_shift_right(v___x_1341_, v___x_1342_);
v_fold_1344_ = lean_uint64_xor(v___x_1341_, v___x_1343_);
v___x_1345_ = 16ULL;
v___x_1346_ = lean_uint64_shift_right(v_fold_1344_, v___x_1345_);
v___x_1347_ = lean_uint64_xor(v_fold_1344_, v___x_1346_);
v___x_1348_ = lean_uint64_to_usize(v___x_1347_);
v___x_1349_ = lean_usize_of_nat(v___x_1340_);
v___x_1350_ = ((size_t)1ULL);
v___x_1351_ = lean_usize_sub(v___x_1349_, v___x_1350_);
v___x_1352_ = lean_usize_land(v___x_1348_, v___x_1351_);
v_bkt_1353_ = lean_array_uget_borrowed(v_buckets_1335_, v___x_1352_);
v___x_1354_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1332_, v_bkt_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; lean_object* v_size_x27_1356_; lean_object* v___x_1357_; lean_object* v_buckets_x27_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1355_ = lean_unsigned_to_nat(1u);
v_size_x27_1356_ = lean_nat_add(v_size_1334_, v___x_1355_);
lean_dec(v_size_1334_);
lean_inc(v_bkt_1353_);
v___x_1357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1332_);
lean_ctor_set(v___x_1357_, 1, v_b_1333_);
lean_ctor_set(v___x_1357_, 2, v_bkt_1353_);
v_buckets_x27_1358_ = lean_array_uset(v_buckets_1335_, v___x_1352_, v___x_1357_);
v___x_1359_ = lean_unsigned_to_nat(4u);
v___x_1360_ = lean_nat_mul(v_size_x27_1356_, v___x_1359_);
v___x_1361_ = lean_unsigned_to_nat(3u);
v___x_1362_ = lean_nat_div(v___x_1360_, v___x_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_array_get_size(v_buckets_x27_1358_);
v___x_1364_ = lean_nat_dec_le(v___x_1362_, v___x_1363_);
lean_dec(v___x_1362_);
if (v___x_1364_ == 0)
{
lean_object* v_val_1365_; lean_object* v___x_1367_; 
v_val_1365_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_buckets_x27_1358_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v_val_1365_);
lean_ctor_set(v___x_1337_, 0, v_size_x27_1356_);
v___x_1367_ = v___x_1337_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_size_x27_1356_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_val_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
lean_object* v___x_1370_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v_buckets_x27_1358_);
lean_ctor_set(v___x_1337_, 0, v_size_x27_1356_);
v___x_1370_ = v___x_1337_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_size_x27_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_buckets_x27_1358_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v_buckets_x27_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_inc(v_bkt_1353_);
v___x_1372_ = lean_box(0);
v_buckets_x27_1373_ = lean_array_uset(v_buckets_1335_, v___x_1352_, v___x_1372_);
v___x_1374_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1332_, v_b_1333_, v_bkt_1353_);
v___x_1375_ = lean_array_uset(v_buckets_x27_1373_, v___x_1352_, v___x_1374_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v___x_1375_);
v___x_1377_ = v___x_1337_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_size_1334_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v___y_1383_; 
switch(lean_obj_tag(v_a_1380_))
{
case 1:
{
lean_dec_ref_known(v_a_1380_, 3);
v___y_1383_ = v_a_1381_;
goto v___jp_1382_;
}
case 2:
{
lean_dec_ref_known(v_a_1380_, 3);
v___y_1383_ = v_a_1381_;
goto v___jp_1382_;
}
case 3:
{
lean_object* v_d_1387_; lean_object* v___x_1388_; 
v_d_1387_ = lean_ctor_get(v_a_1380_, 3);
lean_inc(v_d_1387_);
lean_dec_ref_known(v_a_1380_, 4);
v___x_1388_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1387_, v_a_1381_);
return v___x_1388_;
}
case 4:
{
lean_object* v_d_1389_; lean_object* v___x_1390_; 
v_d_1389_ = lean_ctor_get(v_a_1380_, 2);
lean_inc(v_d_1389_);
lean_dec_ref_known(v_a_1380_, 3);
v___x_1390_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1389_, v_a_1381_);
return v___x_1390_;
}
case 5:
{
lean_object* v_d_1391_; lean_object* v___x_1392_; 
v_d_1391_ = lean_ctor_get(v_a_1380_, 2);
lean_inc(v_d_1391_);
lean_dec_ref_known(v_a_1380_, 3);
v___x_1392_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1391_, v_a_1381_);
return v___x_1392_;
}
case 6:
{
lean_object* v_d_1393_; lean_object* v___x_1394_; 
v_d_1393_ = lean_ctor_get(v_a_1380_, 3);
lean_inc(v_d_1393_);
lean_dec_ref_known(v_a_1380_, 4);
v___x_1394_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1393_, v_a_1381_);
return v___x_1394_;
}
case 7:
{
uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_dec_ref_known(v_a_1380_, 3);
v___x_1395_ = 1;
v___x_1396_ = lean_box(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_a_1381_);
return v___x_1397_;
}
case 8:
{
lean_object* v_d_1398_; lean_object* v___x_1399_; 
v_d_1398_ = lean_ctor_get(v_a_1380_, 2);
lean_inc(v_d_1398_);
lean_dec_ref_known(v_a_1380_, 3);
v___x_1399_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1398_, v_a_1381_);
return v___x_1399_;
}
case 9:
{
lean_object* v_d_1400_; lean_object* v___x_1401_; 
v_d_1400_ = lean_ctor_get(v_a_1380_, 2);
lean_inc(v_d_1400_);
lean_dec_ref_known(v_a_1380_, 3);
v___x_1401_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1400_, v_a_1381_);
return v___x_1401_;
}
case 10:
{
lean_object* v_d_1402_; lean_object* v___x_1403_; 
v_d_1402_ = lean_ctor_get(v_a_1380_, 2);
lean_inc(v_d_1402_);
lean_dec_ref_known(v_a_1380_, 3);
v___x_1403_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1402_, v_a_1381_);
return v___x_1403_;
}
case 11:
{
lean_object* v_d_1404_; lean_object* v___x_1405_; 
v_d_1404_ = lean_ctor_get(v_a_1380_, 3);
lean_inc(v_d_1404_);
lean_dec_ref_known(v_a_1380_, 4);
v___x_1405_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1404_, v_a_1381_);
return v___x_1405_;
}
case 12:
{
lean_object* v_d_1406_; lean_object* v___x_1407_; 
v_d_1406_ = lean_ctor_get(v_a_1380_, 3);
lean_inc(v_d_1406_);
lean_dec_ref_known(v_a_1380_, 4);
v___x_1407_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1406_, v_a_1381_);
return v___x_1407_;
}
case 13:
{
lean_object* v_a_1408_; lean_object* v_b_1409_; lean_object* v___x_1410_; lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v_a_1408_ = lean_ctor_get(v_a_1380_, 2);
lean_inc(v_a_1408_);
v_b_1409_ = lean_ctor_get(v_a_1380_, 3);
lean_inc(v_b_1409_);
lean_dec_ref_known(v_a_1380_, 4);
v___x_1410_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_a_1408_, v_a_1381_);
v_fst_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_fst_1411_);
v_snd_1412_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_snd_1412_);
lean_dec_ref(v___x_1410_);
v___x_1413_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_b_1409_, v_snd_1412_);
v___x_1414_ = lean_unbox(v_fst_1411_);
if (v___x_1414_ == 0)
{
lean_object* v_snd_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
v_snd_1415_ = lean_ctor_get(v___x_1413_, 1);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1413_, 0);
lean_dec(v_unused_1423_);
v___x_1417_ = v___x_1413_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_snd_1415_);
lean_dec(v___x_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v_fst_1411_);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_fst_1411_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_snd_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_dec(v_fst_1411_);
return v___x_1413_;
}
}
default: 
{
uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
lean_dec(v_a_1380_);
v___x_1424_ = 0;
v___x_1425_ = lean_box(v___x_1424_);
v___x_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_a_1381_);
return v___x_1426_;
}
}
v___jp_1382_:
{
uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = 0;
v___x_1385_ = lean_box(v___x_1384_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v___y_1383_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object* v_v_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_cacheKey_1429_; lean_object* v___x_1430_; 
lean_inc(v_v_1427_);
v_cacheKey_1429_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1427_);
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_a_1428_, v_cacheKey_1429_);
if (lean_obj_tag(v___x_1430_) == 1)
{
lean_object* v_val_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_cacheKey_1429_);
lean_dec(v_v_1427_);
v_val_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_val_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_val_1431_);
lean_ctor_set(v___x_1432_, 1, v_a_1428_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v_fst_1434_; lean_object* v_snd_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1443_; 
lean_dec(v___x_1430_);
v___x_1433_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_v_1427_, v_a_1428_);
v_fst_1434_ = lean_ctor_get(v___x_1433_, 0);
v_snd_1435_ = lean_ctor_get(v___x_1433_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1437_ = v___x_1433_;
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snd_1435_);
lean_inc(v_fst_1434_);
lean_dec(v___x_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_inc(v_fst_1434_);
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_snd_1435_, v_cacheKey_1429_, v_fst_1434_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 1, v___x_1439_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_fst_1434_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object* v_00_u03c4_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_a_1445_, v_a_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object* v_00_u03c4_1448_, lean_object* v_v_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1449_, v_a_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object* v_00_u03c4_1452_, lean_object* v_00_u03b2_1453_, lean_object* v_m_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1454_, v_a_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object* v_00_u03c4_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_m_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(v_00_u03c4_1457_, v_00_u03b2_1458_, v_m_1459_, v_a_1460_);
lean_dec_ref(v_a_1460_);
lean_dec_ref(v_m_1459_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object* v_00_u03c4_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_m_1464_, lean_object* v_a_1465_, lean_object* v_b_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_m_1464_, v_a_1465_, v_b_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object* v_00_u03c4_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_a_1470_, lean_object* v_x_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1470_, v_x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object* v_00_u03c4_1473_, lean_object* v_00_u03b2_1474_, lean_object* v_a_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(v_00_u03c4_1473_, v_00_u03b2_1474_, v_a_1475_, v_x_1476_);
lean_dec(v_x_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object* v_00_u03c4_1478_, lean_object* v_00_u03b2_1479_, lean_object* v_a_1480_, lean_object* v_x_1481_){
_start:
{
uint8_t v___x_1482_; 
v___x_1482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1480_, v_x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object* v_00_u03c4_1483_, lean_object* v_00_u03b2_1484_, lean_object* v_a_1485_, lean_object* v_x_1486_){
_start:
{
uint8_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(v_00_u03c4_1483_, v_00_u03b2_1484_, v_a_1485_, v_x_1486_);
lean_dec(v_x_1486_);
lean_dec_ref(v_a_1485_);
v_r_1488_ = lean_box(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object* v_00_u03c4_1489_, lean_object* v_00_u03b2_1490_, lean_object* v_data_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_data_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object* v_00_u03c4_1493_, lean_object* v_00_u03b2_1494_, lean_object* v_a_1495_, lean_object* v_b_1496_, lean_object* v_x_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1495_, v_b_1496_, v_x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object* v_00_u03c4_1499_, lean_object* v_00_u03b2_1500_, lean_object* v_i_1501_, lean_object* v_source_1502_, lean_object* v_target_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v_i_1501_, v_source_1502_, v_target_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03c4_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_x_1507_, v_x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0(void){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_unsigned_to_nat(16u);
v___x_1512_ = lean_mk_array(v___x_1511_, v___x_1510_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0);
v___x_1514_ = lean_unsigned_to_nat(0u);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v___x_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(lean_object* v_v_1516_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_fst_1519_; 
v___x_1517_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1);
v___x_1518_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1516_, v___x_1517_);
v_fst_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_fst_1519_);
lean_dec_ref(v___x_1518_);
return v_fst_1519_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(lean_object* v_00_u03c4_1520_, lean_object* v_inst_1521_, lean_object* v_inst_1522_, lean_object* v_v_1523_){
_start:
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(v_v_1523_);
v___x_1525_ = lean_unbox(v___x_1524_);
lean_dec(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___boxed(lean_object* v_00_u03c4_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_v_1529_){
_start:
{
uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_res_1530_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(v_00_u03c4_1526_, v_inst_1527_, v_inst_1528_, v_v_1529_);
lean_dec_ref(v_inst_1528_);
lean_dec_ref(v_inst_1527_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(uint8_t v_x_1532_){
_start:
{
switch(v_x_1532_)
{
case 0:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_unsigned_to_nat(0u);
return v___x_1533_;
}
case 1:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(1u);
return v___x_1534_;
}
default: 
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_unsigned_to_nat(2u);
return v___x_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1536_){
_start:
{
uint8_t v_x_boxed_1537_; lean_object* v_res_1538_; 
v_x_boxed_1537_ = lean_unbox(v_x_1536_);
v_res_1538_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(v_x_boxed_1537_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object* v_k_1539_){
_start:
{
lean_inc(v_k_1539_);
return v_k_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(v_k_1540_);
lean_dec(v_k_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object* v_motive_1542_, lean_object* v_ctorIdx_1543_, uint8_t v_t_1544_, lean_object* v_h_1545_, lean_object* v_k_1546_){
_start:
{
lean_inc(v_k_1546_);
return v_k_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1547_, lean_object* v_ctorIdx_1548_, lean_object* v_t_1549_, lean_object* v_h_1550_, lean_object* v_k_1551_){
_start:
{
uint8_t v_t_boxed_1552_; lean_object* v_res_1553_; 
v_t_boxed_1552_ = lean_unbox(v_t_1549_);
v_res_1553_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(v_motive_1547_, v_ctorIdx_1548_, v_t_boxed_1552_, v_h_1550_, v_k_1551_);
lean_dec(v_k_1551_);
lean_dec(v_ctorIdx_1548_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1554_){
_start:
{
lean_inc(v_withoutSpacing_1554_);
return v_withoutSpacing_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1555_);
lean_dec(v_withoutSpacing_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1557_, uint8_t v_t_1558_, lean_object* v_h_1559_, lean_object* v_withoutSpacing_1560_){
_start:
{
lean_inc(v_withoutSpacing_1560_);
return v_withoutSpacing_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_withoutSpacing_1564_){
_start:
{
uint8_t v_t_boxed_1565_; lean_object* v_res_1566_; 
v_t_boxed_1565_ = lean_unbox(v_t_1562_);
v_res_1566_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(v_motive_1561_, v_t_boxed_1565_, v_h_1563_, v_withoutSpacing_1564_);
lean_dec(v_withoutSpacing_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object* v_withoutSpacingIfAtomic_1567_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1567_);
return v_withoutSpacingIfAtomic_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object* v_withoutSpacingIfAtomic_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(v_withoutSpacingIfAtomic_1568_);
lean_dec(v_withoutSpacingIfAtomic_1568_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object* v_motive_1570_, uint8_t v_t_1571_, lean_object* v_h_1572_, lean_object* v_withoutSpacingIfAtomic_1573_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1573_);
return v_withoutSpacingIfAtomic_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_withoutSpacingIfAtomic_1577_){
_start:
{
uint8_t v_t_boxed_1578_; lean_object* v_res_1579_; 
v_t_boxed_1578_ = lean_unbox(v_t_1575_);
v_res_1579_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(v_motive_1574_, v_t_boxed_1578_, v_h_1576_, v_withoutSpacingIfAtomic_1577_);
lean_dec(v_withoutSpacingIfAtomic_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1580_){
_start:
{
lean_inc(v_withSpacing_1580_);
return v_withSpacing_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1581_);
lean_dec(v_withSpacing_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object* v_motive_1583_, uint8_t v_t_1584_, lean_object* v_h_1585_, lean_object* v_withSpacing_1586_){
_start:
{
lean_inc(v_withSpacing_1586_);
return v_withSpacing_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1587_, lean_object* v_t_1588_, lean_object* v_h_1589_, lean_object* v_withSpacing_1590_){
_start:
{
uint8_t v_t_boxed_1591_; lean_object* v_res_1592_; 
v_t_boxed_1591_ = lean_unbox(v_t_1588_);
v_res_1592_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(v_motive_1587_, v_t_boxed_1591_, v_h_1589_, v_withSpacing_1590_);
lean_dec(v_withSpacing_1590_);
return v_res_1592_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_unsigned_to_nat(16u);
v___x_1595_ = lean_mk_array(v___x_1594_, v___x_1593_);
return v___x_1595_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0);
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
lean_ctor_set(v___x_1598_, 1, v___x_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object* v_v_1599_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v_fst_1602_; uint8_t v___x_1603_; 
v___x_1600_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1);
v___x_1601_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1599_, v___x_1600_);
v_fst_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_fst_1602_);
lean_dec_ref(v___x_1601_);
v___x_1603_ = lean_unbox(v_fst_1602_);
lean_dec(v_fst_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object* v_v_1604_){
_start:
{
uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_v_1604_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object* v_prefixOperatorTk_1607_, lean_object* v_operand_1608_, uint8_t v_format_1609_){
_start:
{
lean_object* v___y_1611_; uint8_t v___y_1630_; uint8_t v___x_1631_; 
v___x_1631_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_prefixOperatorTk_1607_);
if (v___x_1631_ == 0)
{
if (v_format_1609_ == 0)
{
goto v___jp_1615_;
}
else
{
if (v___x_1631_ == 0)
{
if (v_format_1609_ == 1)
{
uint8_t v___x_1632_; 
v___x_1632_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_operand_1608_);
if (v___x_1632_ == 0)
{
v___y_1630_ = v___x_1632_;
goto v___jp_1629_;
}
else
{
uint8_t v___x_1633_; 
lean_inc_ref(v_operand_1608_);
v___x_1633_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_operand_1608_);
if (v___x_1633_ == 0)
{
v___y_1630_ = v___x_1632_;
goto v___jp_1629_;
}
else
{
goto v___jp_1622_;
}
}
}
else
{
goto v___jp_1622_;
}
}
else
{
goto v___jp_1615_;
}
}
}
else
{
lean_dec_ref(v_prefixOperatorTk_1607_);
return v_operand_1608_;
}
v___jp_1610_:
{
lean_object* v_doc_1612_; uint8_t v___x_1613_; 
v_doc_1612_ = lean_ctor_get(v_operand_1608_, 0);
lean_inc(v_doc_1612_);
lean_dec_ref(v_operand_1608_);
v___x_1613_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1612_);
if (v___x_1613_ == 0)
{
return v___y_1611_;
}
else
{
lean_object* v_doc_1614_; 
v_doc_1614_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___y_1611_);
return v_doc_1614_;
}
}
v___jp_1615_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1616_ = lean_unsigned_to_nat(2u);
v___x_1617_ = lean_mk_empty_array_with_capacity(v___x_1616_);
v___x_1618_ = lean_array_push(v___x_1617_, v_prefixOperatorTk_1607_);
lean_inc_ref(v_operand_1608_);
v___x_1619_ = lean_array_push(v___x_1618_, v_operand_1608_);
v___x_1620_ = l_Lean_Fmt_Layouts_atomic(v___x_1619_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1620_);
v___y_1611_ = v___x_1621_;
goto v___jp_1610_;
}
v___jp_1622_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1623_ = lean_unsigned_to_nat(2u);
v___x_1624_ = lean_mk_empty_array_with_capacity(v___x_1623_);
v___x_1625_ = lean_array_push(v___x_1624_, v_prefixOperatorTk_1607_);
lean_inc_ref(v_operand_1608_);
v___x_1626_ = lean_array_push(v___x_1625_, v_operand_1608_);
v___x_1627_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1626_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1627_);
v___y_1611_ = v___x_1628_;
goto v___jp_1610_;
}
v___jp_1629_:
{
if (v___y_1630_ == 0)
{
goto v___jp_1622_;
}
else
{
goto v___jp_1615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object* v_prefixOperatorTk_1634_, lean_object* v_operand_1635_, lean_object* v_format_1636_){
_start:
{
uint8_t v_format_boxed_1637_; lean_object* v_res_1638_; 
v_format_boxed_1637_ = lean_unbox(v_format_1636_);
v_res_1638_ = l_Lean_Fmt_Layouts_prefixOperator(v_prefixOperatorTk_1634_, v_operand_1635_, v_format_boxed_1637_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(uint8_t v_x_1639_){
_start:
{
if (v_x_1639_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_unsigned_to_nat(0u);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_unsigned_to_nat(1u);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1642_){
_start:
{
uint8_t v_x_boxed_1643_; lean_object* v_res_1644_; 
v_x_boxed_1643_ = lean_unbox(v_x_1642_);
v_res_1644_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(v_x_boxed_1643_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object* v_k_1645_){
_start:
{
lean_inc(v_k_1645_);
return v_k_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(v_k_1646_);
lean_dec(v_k_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object* v_motive_1648_, lean_object* v_ctorIdx_1649_, uint8_t v_t_1650_, lean_object* v_h_1651_, lean_object* v_k_1652_){
_start:
{
lean_inc(v_k_1652_);
return v_k_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1653_, lean_object* v_ctorIdx_1654_, lean_object* v_t_1655_, lean_object* v_h_1656_, lean_object* v_k_1657_){
_start:
{
uint8_t v_t_boxed_1658_; lean_object* v_res_1659_; 
v_t_boxed_1658_ = lean_unbox(v_t_1655_);
v_res_1659_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(v_motive_1653_, v_ctorIdx_1654_, v_t_boxed_1658_, v_h_1656_, v_k_1657_);
lean_dec(v_k_1657_);
lean_dec(v_ctorIdx_1654_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1660_){
_start:
{
lean_inc(v_withoutSpacing_1660_);
return v_withoutSpacing_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1661_);
lean_dec(v_withoutSpacing_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1663_, uint8_t v_t_1664_, lean_object* v_h_1665_, lean_object* v_withoutSpacing_1666_){
_start:
{
lean_inc(v_withoutSpacing_1666_);
return v_withoutSpacing_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1667_, lean_object* v_t_1668_, lean_object* v_h_1669_, lean_object* v_withoutSpacing_1670_){
_start:
{
uint8_t v_t_boxed_1671_; lean_object* v_res_1672_; 
v_t_boxed_1671_ = lean_unbox(v_t_1668_);
v_res_1672_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(v_motive_1667_, v_t_boxed_1671_, v_h_1669_, v_withoutSpacing_1670_);
lean_dec(v_withoutSpacing_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1673_){
_start:
{
lean_inc(v_withSpacing_1673_);
return v_withSpacing_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1674_);
lean_dec(v_withSpacing_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object* v_motive_1676_, uint8_t v_t_1677_, lean_object* v_h_1678_, lean_object* v_withSpacing_1679_){
_start:
{
lean_inc(v_withSpacing_1679_);
return v_withSpacing_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1680_, lean_object* v_t_1681_, lean_object* v_h_1682_, lean_object* v_withSpacing_1683_){
_start:
{
uint8_t v_t_boxed_1684_; lean_object* v_res_1685_; 
v_t_boxed_1684_ = lean_unbox(v_t_1681_);
v_res_1685_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(v_motive_1680_, v_t_boxed_1684_, v_h_1682_, v_withSpacing_1683_);
lean_dec(v_withSpacing_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object* v_operand_1686_, lean_object* v_postfixOperatorTk_1687_, uint8_t v_format_1688_){
_start:
{
uint8_t v___x_1696_; 
v___x_1696_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_postfixOperatorTk_1687_);
if (v___x_1696_ == 0)
{
if (v_format_1688_ == 1)
{
goto v___jp_1689_;
}
else
{
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1697_ = lean_unsigned_to_nat(2u);
v___x_1698_ = lean_mk_empty_array_with_capacity(v___x_1697_);
v___x_1699_ = lean_array_push(v___x_1698_, v_operand_1686_);
v___x_1700_ = lean_array_push(v___x_1699_, v_postfixOperatorTk_1687_);
v___x_1701_ = l_Lean_Fmt_Layouts_atomic(v___x_1700_);
lean_dec_ref(v___x_1700_);
v___x_1702_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1701_);
return v___x_1702_;
}
else
{
goto v___jp_1689_;
}
}
}
else
{
lean_dec_ref(v_postfixOperatorTk_1687_);
return v_operand_1686_;
}
v___jp_1689_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1690_ = lean_unsigned_to_nat(2u);
v___x_1691_ = lean_mk_empty_array_with_capacity(v___x_1690_);
v___x_1692_ = lean_array_push(v___x_1691_, v_operand_1686_);
v___x_1693_ = lean_array_push(v___x_1692_, v_postfixOperatorTk_1687_);
v___x_1694_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1694_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object* v_operand_1703_, lean_object* v_postfixOperatorTk_1704_, lean_object* v_format_1705_){
_start:
{
uint8_t v_format_boxed_1706_; lean_object* v_res_1707_; 
v_format_boxed_1706_ = lean_unbox(v_format_1705_);
v_res_1707_ = l_Lean_Fmt_Layouts_postfixOperator(v_operand_1703_, v_postfixOperatorTk_1704_, v_format_boxed_1706_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(lean_object* v_x_1708_){
_start:
{
if (lean_obj_tag(v_x_1708_) == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_unsigned_to_nat(0u);
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_unsigned_to_nat(1u);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(v_x_1711_);
lean_dec_ref(v_x_1711_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object* v_t_1713_, lean_object* v_k_1714_){
_start:
{
uint8_t v_hardNestedFirstOperand_1715_; uint8_t v_trailingOperator_1716_; uint8_t v_spacing_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_hardNestedFirstOperand_1715_ = lean_ctor_get_uint8(v_t_1713_, 0);
v_trailingOperator_1716_ = lean_ctor_get_uint8(v_t_1713_, 1);
v_spacing_1717_ = lean_ctor_get_uint8(v_t_1713_, 2);
v___x_1718_ = lean_box(v_hardNestedFirstOperand_1715_);
v___x_1719_ = lean_box(v_trailingOperator_1716_);
v___x_1720_ = lean_box(v_spacing_1717_);
v___x_1721_ = lean_apply_3(v_k_1714_, v___x_1718_, v___x_1719_, v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_t_1722_, lean_object* v_k_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1722_, v_k_1723_);
lean_dec_ref(v_t_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object* v_motive_1725_, lean_object* v_ctorIdx_1726_, lean_object* v_t_1727_, lean_object* v_h_1728_, lean_object* v_k_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1727_, v_k_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1731_, lean_object* v_ctorIdx_1732_, lean_object* v_t_1733_, lean_object* v_h_1734_, lean_object* v_k_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(v_motive_1731_, v_ctorIdx_1732_, v_t_1733_, v_h_1734_, v_k_1735_);
lean_dec_ref(v_t_1733_);
lean_dec(v_ctorIdx_1732_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object* v_t_1737_, lean_object* v_dense_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1737_, v_dense_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object* v_t_1740_, lean_object* v_dense_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(v_t_1740_, v_dense_1741_);
lean_dec_ref(v_t_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object* v_motive_1743_, lean_object* v_t_1744_, lean_object* v_h_1745_, lean_object* v_dense_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1744_, v_dense_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object* v_motive_1748_, lean_object* v_t_1749_, lean_object* v_h_1750_, lean_object* v_dense_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(v_motive_1748_, v_t_1749_, v_h_1750_, v_dense_1751_);
lean_dec_ref(v_t_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object* v_t_1753_, lean_object* v_sparse_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1753_, v_sparse_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object* v_t_1756_, lean_object* v_sparse_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(v_t_1756_, v_sparse_1757_);
lean_dec_ref(v_t_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object* v_motive_1759_, lean_object* v_t_1760_, lean_object* v_h_1761_, lean_object* v_sparse_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1760_, v_sparse_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object* v_motive_1764_, lean_object* v_t_1765_, lean_object* v_h_1766_, lean_object* v_sparse_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(v_motive_1764_, v_t_1765_, v_h_1766_, v_sparse_1767_);
lean_dec_ref(v_t_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object* v_x_1769_){
_start:
{
uint8_t v_hardNestedFirstOperand_1770_; 
v_hardNestedFirstOperand_1770_ = lean_ctor_get_uint8(v_x_1769_, 0);
return v_hardNestedFirstOperand_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object* v_x_1771_){
_start:
{
uint8_t v_res_1772_; lean_object* v_r_1773_; 
v_res_1772_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(v_x_1771_);
lean_dec_ref(v_x_1771_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object* v_x_1774_){
_start:
{
uint8_t v_trailingOperator_1775_; 
v_trailingOperator_1775_ = lean_ctor_get_uint8(v_x_1774_, 1);
return v_trailingOperator_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object* v_x_1776_){
_start:
{
uint8_t v_res_1777_; lean_object* v_r_1778_; 
v_res_1777_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(v_x_1776_);
lean_dec_ref(v_x_1776_);
v_r_1778_ = lean_box(v_res_1777_);
return v_r_1778_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object* v_x_1779_){
_start:
{
uint8_t v_spacing_1780_; 
v_spacing_1780_ = lean_ctor_get_uint8(v_x_1779_, 2);
return v_spacing_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object* v_x_1781_){
_start:
{
uint8_t v_res_1782_; lean_object* v_r_1783_; 
v_res_1782_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(v_x_1781_);
lean_dec_ref(v_x_1781_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object* v_doc_1784_, uint8_t v_respectPseudoAlignment_1785_){
_start:
{
if (v_respectPseudoAlignment_1785_ == 0)
{
lean_object* v_doc_1786_; uint8_t v___x_1787_; 
v_doc_1786_ = lean_ctor_get(v_doc_1784_, 0);
lean_inc(v_doc_1786_);
lean_dec_ref(v_doc_1784_);
v___x_1787_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1786_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = 1;
return v___x_1788_;
}
else
{
return v_respectPseudoAlignment_1785_;
}
}
else
{
uint8_t v___x_1789_; 
lean_inc_ref(v_doc_1784_);
v___x_1789_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_1784_);
if (v___x_1789_ == 0)
{
lean_object* v_doc_1790_; uint8_t v___x_1791_; 
v_doc_1790_ = lean_ctor_get(v_doc_1784_, 0);
lean_inc(v_doc_1790_);
lean_dec_ref(v_doc_1784_);
v___x_1791_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1790_);
if (v___x_1791_ == 0)
{
return v_respectPseudoAlignment_1785_;
}
else
{
return v___x_1789_;
}
}
else
{
uint8_t v___x_1792_; 
lean_dec_ref(v_doc_1784_);
v___x_1792_ = 0;
return v___x_1792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object* v_doc_1793_, lean_object* v_respectPseudoAlignment_1794_){
_start:
{
uint8_t v_respectPseudoAlignment_boxed_1795_; uint8_t v_res_1796_; lean_object* v_r_1797_; 
v_respectPseudoAlignment_boxed_1795_ = lean_unbox(v_respectPseudoAlignment_1794_);
v_res_1796_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_doc_1793_, v_respectPseudoAlignment_boxed_1795_);
v_r_1797_ = lean_box(v_res_1796_);
return v_r_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object* v_format_1798_, lean_object* v_docs_1799_){
_start:
{
uint8_t v___y_1801_; uint8_t v_spacing_1804_; 
v_spacing_1804_ = lean_ctor_get_uint8(v_format_1798_, 2);
v___y_1801_ = v_spacing_1804_;
goto v___jp_1800_;
v___jp_1800_:
{
if (v___y_1801_ == 0)
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Fmt_Layouts_atomic(v_docs_1799_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Fmt_Layouts_spacedAtomic(v_docs_1799_);
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object* v_format_1805_, lean_object* v_docs_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1805_, v_docs_1806_);
lean_dec_ref(v_docs_1806_);
lean_dec_ref(v_format_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object* v_msg_1808_){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_1810_ = lean_panic_fn_borrowed(v___x_1809_, v_msg_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t v_a_1811_, lean_object* v_as_1812_, size_t v_i_1813_, size_t v_stop_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_usize_dec_eq(v_i_1813_, v_stop_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; uint8_t v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_array_uget_borrowed(v_as_1812_, v_i_1813_);
v___x_1817_ = lean_unbox(v___x_1816_);
v___x_1818_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_a_1811_, v___x_1817_);
if (v___x_1818_ == 0)
{
size_t v___x_1819_; size_t v___x_1820_; 
v___x_1819_ = ((size_t)1ULL);
v___x_1820_ = lean_usize_add(v_i_1813_, v___x_1819_);
v_i_1813_ = v___x_1820_;
goto _start;
}
else
{
return v___x_1818_;
}
}
else
{
uint8_t v___x_1822_; 
v___x_1822_ = 0;
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object* v_a_1823_, lean_object* v_as_1824_, lean_object* v_i_1825_, lean_object* v_stop_1826_){
_start:
{
uint8_t v_a_boxed_1827_; size_t v_i_boxed_1828_; size_t v_stop_boxed_1829_; uint8_t v_res_1830_; lean_object* v_r_1831_; 
v_a_boxed_1827_ = lean_unbox(v_a_1823_);
v_i_boxed_1828_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_stop_boxed_1829_ = lean_unbox_usize(v_stop_1826_);
lean_dec(v_stop_1826_);
v_res_1830_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_boxed_1827_, v_as_1824_, v_i_boxed_1828_, v_stop_boxed_1829_);
lean_dec_ref(v_as_1824_);
v_r_1831_ = lean_box(v_res_1830_);
return v_r_1831_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object* v_as_1832_, uint8_t v_a_1833_){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_array_get_size(v_as_1832_);
v___x_1836_ = lean_nat_dec_lt(v___x_1834_, v___x_1835_);
if (v___x_1836_ == 0)
{
return v___x_1836_;
}
else
{
if (v___x_1836_ == 0)
{
return v___x_1836_;
}
else
{
size_t v___x_1837_; size_t v___x_1838_; uint8_t v___x_1839_; 
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = lean_usize_of_nat(v___x_1835_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_1833_, v_as_1832_, v___x_1837_, v___x_1838_);
return v___x_1839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object* v_as_1840_, lean_object* v_a_1841_){
_start:
{
uint8_t v_a_boxed_1842_; uint8_t v_res_1843_; lean_object* v_r_1844_; 
v_a_boxed_1842_ = lean_unbox(v_a_1841_);
v_res_1843_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_as_1840_, v_a_boxed_1842_);
lean_dec_ref(v_as_1840_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1848_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2));
v___x_1849_ = lean_unsigned_to_nat(14u);
v___x_1850_ = lean_unsigned_to_nat(22u);
v___x_1851_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1));
v___x_1852_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_1853_ = l_mkPanicMessageWithDecl(v___x_1852_, v___x_1851_, v___x_1850_, v___x_1849_, v___x_1848_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object* v_format_1854_, lean_object* v_doc_1855_, lean_object* v_lastOperand_1856_, uint8_t v_isTailless_1857_, lean_object* v_combinedChain_1858_, lean_object* v_eligibleKinds_1859_){
_start:
{
lean_object* v___x_1860_; uint8_t v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1884_; uint8_t v_trailingOperator_1897_; 
v___x_1860_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_1897_ = lean_ctor_get_uint8(v_format_1854_, 1);
v___y_1884_ = v_trailingOperator_1897_;
goto v___jp_1883_;
v___jp_1861_:
{
lean_object* v_stickyVariant_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_stickyVariant_1864_ = lean_ctor_get(v___y_1863_, 0);
v___x_1865_ = lean_array_get_size(v_combinedChain_1858_);
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_sub(v___x_1865_, v___x_1866_);
lean_inc_ref(v_stickyVariant_1864_);
v___x_1868_ = lean_array_set(v_combinedChain_1858_, v___x_1867_, v_stickyVariant_1864_);
lean_dec(v___x_1867_);
lean_inc_ref(v___x_1868_);
v___x_1869_ = lean_array_pop(v___x_1868_);
v___x_1870_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1854_, v___x_1869_);
lean_dec_ref(v___x_1869_);
v___x_1871_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1870_);
v___x_1872_ = lean_array_get_size(v___x_1868_);
v___x_1873_ = lean_nat_sub(v___x_1872_, v___x_1866_);
v___x_1874_ = lean_array_get(v___x_1860_, v___x_1868_, v___x_1873_);
lean_dec(v___x_1873_);
lean_dec_ref(v___x_1868_);
v___x_1875_ = lean_unsigned_to_nat(2u);
v___x_1876_ = lean_mk_empty_array_with_capacity(v___x_1875_);
v___x_1877_ = lean_array_push(v___x_1876_, v___x_1871_);
v___x_1878_ = lean_array_push(v___x_1877_, v___x_1874_);
v___x_1879_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1854_, v___x_1878_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_1863_, v___y_1862_);
lean_dec_ref(v___y_1863_);
v___x_1881_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_1855_, v___x_1879_, v___x_1880_);
lean_dec(v___x_1880_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
return v___x_1882_;
}
v___jp_1883_:
{
if (v___y_1884_ == 0)
{
lean_object* v___x_1885_; 
lean_dec_ref(v_combinedChain_1858_);
lean_dec_ref(v_lastOperand_1856_);
lean_dec_ref(v_doc_1855_);
v___x_1885_ = lean_box(0);
return v___x_1885_;
}
else
{
if (v_isTailless_1857_ == 0)
{
lean_object* v___x_1886_; 
lean_inc_ref(v_lastOperand_1856_);
v___x_1886_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v_lastOperand_1856_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref(v_combinedChain_1858_);
lean_dec_ref(v_lastOperand_1856_);
lean_dec_ref(v_doc_1855_);
v___x_1887_ = lean_box(0);
return v___x_1887_;
}
else
{
lean_object* v_val_1888_; uint8_t v___x_1889_; uint8_t v___x_1890_; 
v_val_1888_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v___x_1886_, 1);
v___x_1889_ = lean_unbox(v_val_1888_);
lean_dec(v_val_1888_);
v___x_1890_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_1859_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v_combinedChain_1858_);
lean_dec_ref(v_lastOperand_1856_);
lean_dec_ref(v_doc_1855_);
v___x_1891_ = lean_box(0);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_lastOperand_1856_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_1894_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_1893_);
v___y_1862_ = v___x_1890_;
v___y_1863_ = v___x_1894_;
goto v___jp_1861_;
}
else
{
lean_object* v_val_1895_; 
v_val_1895_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v___x_1892_, 1);
v___y_1862_ = v___x_1890_;
v___y_1863_ = v_val_1895_;
goto v___jp_1861_;
}
}
}
}
else
{
lean_object* v___x_1896_; 
lean_dec_ref(v_combinedChain_1858_);
lean_dec_ref(v_lastOperand_1856_);
lean_dec_ref(v_doc_1855_);
v___x_1896_ = lean_box(0);
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object* v_format_1898_, lean_object* v_doc_1899_, lean_object* v_lastOperand_1900_, lean_object* v_isTailless_1901_, lean_object* v_combinedChain_1902_, lean_object* v_eligibleKinds_1903_){
_start:
{
uint8_t v_isTailless_boxed_1904_; lean_object* v_res_1905_; 
v_isTailless_boxed_1904_ = lean_unbox(v_isTailless_1901_);
v_res_1905_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_1898_, v_doc_1899_, v_lastOperand_1900_, v_isTailless_boxed_1904_, v_combinedChain_1902_, v_eligibleKinds_1903_);
lean_dec_ref(v_eligibleKinds_1903_);
lean_dec_ref(v_format_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object* v_format_1906_, lean_object* v_doc_1907_, lean_object* v_lastOperand_1908_, uint8_t v_isTailless_1909_, lean_object* v_combinedChain_1910_){
_start:
{
if (lean_obj_tag(v_format_1906_) == 0)
{
if (v_isTailless_1909_ == 0)
{
uint8_t v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = 1;
v___x_1912_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_lastOperand_1908_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref(v_combinedChain_1910_);
lean_dec_ref(v_doc_1907_);
v___x_1913_ = lean_box(0);
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1914_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
lean_inc_ref(v_combinedChain_1910_);
v___x_1915_ = lean_array_pop(v_combinedChain_1910_);
v___x_1916_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1906_, v___x_1915_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1916_);
v___x_1918_ = lean_array_get_size(v_combinedChain_1910_);
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_nat_sub(v___x_1918_, v___x_1919_);
v___x_1921_ = lean_array_get(v___x_1914_, v_combinedChain_1910_, v___x_1920_);
lean_dec(v___x_1920_);
lean_dec_ref(v_combinedChain_1910_);
v___x_1922_ = lean_unsigned_to_nat(2u);
v___x_1923_ = lean_mk_empty_array_with_capacity(v___x_1922_);
v___x_1924_ = lean_array_push(v___x_1923_, v___x_1917_);
v___x_1925_ = lean_array_push(v___x_1924_, v___x_1921_);
v___x_1926_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_1906_, v___x_1925_);
lean_dec_ref(v___x_1925_);
v___x_1927_ = l_Lean_Fmt_TaggedDoc_fallbackOnHeight(v_doc_1907_, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
}
else
{
lean_object* v___x_1929_; 
lean_dec_ref(v_combinedChain_1910_);
lean_dec_ref(v_lastOperand_1908_);
lean_dec_ref(v_doc_1907_);
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
}
else
{
lean_object* v___x_1930_; 
lean_dec_ref(v_combinedChain_1910_);
lean_dec_ref(v_lastOperand_1908_);
lean_dec_ref(v_doc_1907_);
v___x_1930_ = lean_box(0);
return v___x_1930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object* v_format_1931_, lean_object* v_doc_1932_, lean_object* v_lastOperand_1933_, lean_object* v_isTailless_1934_, lean_object* v_combinedChain_1935_){
_start:
{
uint8_t v_isTailless_boxed_1936_; lean_object* v_res_1937_; 
v_isTailless_boxed_1936_ = lean_unbox(v_isTailless_1934_);
v_res_1937_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_1931_, v_doc_1932_, v_lastOperand_1933_, v_isTailless_boxed_1936_, v_combinedChain_1935_);
lean_dec_ref(v_format_1931_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object* v_snd_1938_, lean_object* v___x_1939_, lean_object* v_____r_1940_, lean_object* v_normalized_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_nat_add(v_snd_1938_, v___x_1939_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_normalized_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object* v_snd_1945_, lean_object* v___x_1946_, lean_object* v_____r_1947_, lean_object* v_normalized_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1945_, v___x_1946_, v_____r_1947_, v_normalized_1948_);
lean_dec(v___x_1946_);
lean_dec(v_snd_1945_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object* v___x_1950_, lean_object* v_chain_1951_, lean_object* v___x_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___y_1955_; lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1990_; 
v_fst_1959_ = lean_ctor_get(v_a_1953_, 0);
v_snd_1960_ = lean_ctor_get(v_a_1953_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_a_1953_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1962_ = v_a_1953_;
v_isShared_1963_ = v_isSharedCheck_1990_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_inc(v_fst_1959_);
lean_dec(v_a_1953_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1990_;
goto v_resetjp_1961_;
}
v___jp_1954_:
{
if (lean_obj_tag(v___y_1955_) == 0)
{
lean_object* v_a_1956_; 
v_a_1956_ = lean_ctor_get(v___y_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___y_1955_, 1);
return v_a_1956_;
}
else
{
lean_object* v_a_1957_; 
v_a_1957_ = lean_ctor_get(v___y_1955_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___y_1955_, 1);
v_a_1953_ = v_a_1957_;
goto _start;
}
}
v_resetjp_1961_:
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_nat_dec_lt(v_snd_1960_, v___x_1950_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1966_; 
if (v_isShared_1963_ == 0)
{
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_fst_1959_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_snd_1960_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1968_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1969_ = lean_array_get_borrowed(v___x_1968_, v_chain_1951_, v_snd_1960_);
v___x_1970_ = lean_unsigned_to_nat(1u);
v___x_1971_ = lean_nat_add(v_snd_1960_, v___x_1970_);
v___x_1972_ = lean_array_get_size(v_chain_1951_);
v___x_1973_ = lean_nat_dec_lt(v___x_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_dec(v___x_1971_);
lean_inc(v___x_1969_);
v___x_1974_ = lean_array_push(v_fst_1959_, v___x_1969_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1974_);
v___x_1976_ = v___x_1962_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_snd_1960_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; uint8_t v___x_1985_; 
lean_del_object(v___x_1962_);
v___x_1978_ = lean_unsigned_to_nat(2u);
v___x_1979_ = lean_array_fget_borrowed(v_chain_1951_, v___x_1971_);
lean_dec(v___x_1971_);
v___x_1985_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_1979_);
if (v___x_1985_ == 0)
{
goto v___jp_1980_;
}
else
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = lean_nat_dec_eq(v___x_1952_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_box(0);
v___x_1989_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1960_, v___x_1978_, v___x_1988_, v_fst_1959_);
lean_dec(v_snd_1960_);
v___y_1955_ = v___x_1989_;
goto v___jp_1954_;
}
else
{
goto v___jp_1980_;
}
}
v___jp_1980_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_inc(v___x_1969_);
v___x_1981_ = lean_array_push(v_fst_1959_, v___x_1969_);
lean_inc(v___x_1979_);
v___x_1982_ = lean_array_push(v___x_1981_, v___x_1979_);
v___x_1983_ = lean_box(0);
v___x_1984_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_1960_, v___x_1978_, v___x_1983_, v___x_1982_);
lean_dec(v_snd_1960_);
v___y_1955_ = v___x_1984_;
goto v___jp_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object* v___x_1991_, lean_object* v_chain_1992_, lean_object* v___x_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_1991_, v_chain_1992_, v___x_1993_, v_a_1994_);
lean_dec(v___x_1993_);
lean_dec_ref(v_chain_1992_);
lean_dec(v___x_1991_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object* v___x_1996_, lean_object* v_chain_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v___y_2000_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2032_; 
v_fst_2004_ = lean_ctor_get(v_a_1998_, 0);
v_snd_2005_ = lean_ctor_get(v_a_1998_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_1998_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2007_ = v_a_1998_;
v_isShared_2008_ = v_isSharedCheck_2032_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_snd_2005_);
lean_inc(v_fst_2004_);
lean_dec(v_a_1998_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2032_;
goto v_resetjp_2006_;
}
v___jp_1999_:
{
if (lean_obj_tag(v___y_2000_) == 0)
{
lean_object* v_a_2001_; 
v_a_2001_ = lean_ctor_get(v___y_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___y_2000_, 1);
return v_a_2001_;
}
else
{
lean_object* v_a_2002_; 
v_a_2002_ = lean_ctor_get(v___y_2000_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___y_2000_, 1);
v_a_1998_ = v_a_2002_;
goto _start;
}
}
v_resetjp_2006_:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_nat_dec_lt(v_snd_2005_, v___x_1996_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2011_; 
if (v_isShared_2008_ == 0)
{
v___x_2011_ = v___x_2007_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_fst_2004_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_snd_2005_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2013_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2014_ = lean_array_get_borrowed(v___x_2013_, v_chain_1997_, v_snd_2005_);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_add(v_snd_2005_, v___x_2015_);
v___x_2017_ = lean_array_get_size(v_chain_1997_);
v___x_2018_ = lean_nat_dec_lt(v___x_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_dec(v___x_2016_);
lean_inc(v___x_2014_);
v___x_2019_ = lean_array_push(v_fst_2004_, v___x_2014_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2019_);
v___x_2021_ = v___x_2007_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_snd_2005_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
lean_del_object(v___x_2007_);
v___x_2023_ = lean_unsigned_to_nat(2u);
v___x_2024_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2014_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2025_ = lean_array_fget_borrowed(v_chain_1997_, v___x_2016_);
lean_dec(v___x_2016_);
lean_inc(v___x_2014_);
v___x_2026_ = lean_array_push(v_fst_2004_, v___x_2014_);
lean_inc(v___x_2025_);
v___x_2027_ = lean_array_push(v___x_2026_, v___x_2025_);
v___x_2028_ = lean_box(0);
v___x_2029_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2005_, v___x_2023_, v___x_2028_, v___x_2027_);
lean_dec(v_snd_2005_);
v___y_2000_ = v___x_2029_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v___x_2016_);
v___x_2030_ = lean_box(0);
v___x_2031_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2005_, v___x_2023_, v___x_2030_, v_fst_2004_);
lean_dec(v_snd_2005_);
v___y_2000_ = v___x_2031_;
goto v___jp_1999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object* v___x_2033_, lean_object* v_chain_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2033_, v_chain_2034_, v_a_2035_);
lean_dec_ref(v_chain_2034_);
lean_dec(v___x_2033_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object* v_format_2045_, lean_object* v_chain_2046_){
_start:
{
lean_object* v___y_2048_; lean_object* v___y_2049_; uint8_t v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2069_; lean_object* v___y_2070_; uint8_t v___y_2071_; uint8_t v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___f_2089_; lean_object* v_chainSizeBeforeSuffixTrim_2090_; lean_object* v_chain_2091_; lean_object* v_chainSizeBeforePrefixTrim_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___y_2098_; uint8_t v___y_2099_; uint8_t v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2110_; uint8_t v___y_2111_; uint8_t v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2114_; uint8_t v___y_2115_; lean_object* v___y_2123_; uint8_t v___y_2124_; lean_object* v___y_2125_; uint8_t v___y_2126_; uint8_t v___y_2131_; uint8_t v___x_2141_; 
v___f_2089_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0));
v_chainSizeBeforeSuffixTrim_2090_ = lean_array_get_size(v_chain_2046_);
v_chain_2091_ = l_Array_popWhile___redArg(v___f_2089_, v_chain_2046_);
v_chainSizeBeforePrefixTrim_2092_ = lean_array_get_size(v_chain_2091_);
v___x_2093_ = lean_nat_sub(v_chainSizeBeforeSuffixTrim_2090_, v_chainSizeBeforePrefixTrim_2092_);
v___x_2094_ = lean_unsigned_to_nat(2u);
v___x_2095_ = lean_nat_mod(v___x_2093_, v___x_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2141_ = lean_nat_dec_eq(v___x_2095_, v___x_2096_);
lean_dec(v___x_2095_);
if (v___x_2141_ == 0)
{
uint8_t v___x_2142_; 
v___x_2142_ = 1;
v___y_2131_ = v___x_2142_;
goto v___jp_2130_;
}
else
{
uint8_t v___x_2143_; 
v___x_2143_ = 0;
v___y_2131_ = v___x_2143_;
goto v___jp_2130_;
}
v___jp_2047_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v_fst_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2066_; 
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___y_2049_);
lean_ctor_set(v___x_2054_, 1, v___y_2053_);
v___x_2055_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___y_2052_, v___y_2048_, v___y_2052_, v___x_2054_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2052_);
v_fst_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v___x_2055_, 1);
lean_dec(v_unused_2067_);
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_fst_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2060_ = lean_box(v___y_2050_);
v___x_2061_ = lean_box(v___y_2051_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v___x_2061_);
lean_ctor_set(v___x_2058_, 0, v___x_2060_);
v___x_2063_ = v___x_2058_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_fst_2056_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
return v___x_2064_;
}
}
}
v___jp_2068_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v_fst_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2087_; 
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___y_2070_);
lean_ctor_set(v___x_2075_, 1, v___y_2074_);
v___x_2076_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___y_2073_, v___y_2069_, v___x_2075_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2073_);
v_fst_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2076_, 1);
lean_dec(v_unused_2088_);
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_fst_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2081_ = lean_box(v___y_2071_);
v___x_2082_ = lean_box(v___y_2072_);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2082_);
lean_ctor_set(v___x_2079_, 0, v___x_2081_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v_fst_2077_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
return v___x_2085_;
}
}
}
v___jp_2097_:
{
if (v___y_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2103_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2104_ = lean_array_get_borrowed(v___x_2103_, v___y_2098_, v___x_2096_);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_mk_empty_array_with_capacity(v___x_2105_);
lean_inc(v___x_2104_);
v___x_2107_ = lean_array_push(v___x_2106_, v___x_2104_);
v___y_2048_ = v___y_2098_;
v___y_2049_ = v___x_2107_;
v___y_2050_ = v___y_2099_;
v___y_2051_ = v___y_2100_;
v___y_2052_ = v___y_2101_;
v___y_2053_ = v___x_2105_;
goto v___jp_2047_;
}
else
{
lean_object* v___x_2108_; 
v___x_2108_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2048_ = v___y_2098_;
v___y_2049_ = v___x_2108_;
v___y_2050_ = v___y_2099_;
v___y_2051_ = v___y_2100_;
v___y_2052_ = v___y_2101_;
v___y_2053_ = v___x_2096_;
goto v___jp_2047_;
}
}
v___jp_2109_:
{
if (v___y_2115_ == 0)
{
v___y_2098_ = v___y_2110_;
v___y_2099_ = v___y_2111_;
v___y_2100_ = v___y_2113_;
v___y_2101_ = v___y_2114_;
v___y_2102_ = v___y_2111_;
goto v___jp_2097_;
}
else
{
if (v___y_2112_ == 0)
{
if (v___y_2111_ == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2069_ = v___y_2110_;
v___y_2070_ = v___x_2116_;
v___y_2071_ = v___y_2111_;
v___y_2072_ = v___y_2113_;
v___y_2073_ = v___y_2114_;
v___y_2074_ = v___x_2096_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2117_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2118_ = lean_array_get_borrowed(v___x_2117_, v___y_2110_, v___x_2096_);
v___x_2119_ = lean_unsigned_to_nat(1u);
v___x_2120_ = lean_mk_empty_array_with_capacity(v___x_2119_);
lean_inc(v___x_2118_);
v___x_2121_ = lean_array_push(v___x_2120_, v___x_2118_);
v___y_2069_ = v___y_2110_;
v___y_2070_ = v___x_2121_;
v___y_2071_ = v___y_2111_;
v___y_2072_ = v___y_2113_;
v___y_2073_ = v___y_2114_;
v___y_2074_ = v___x_2119_;
goto v___jp_2068_;
}
}
else
{
v___y_2098_ = v___y_2110_;
v___y_2099_ = v___y_2111_;
v___y_2100_ = v___y_2113_;
v___y_2101_ = v___y_2114_;
v___y_2102_ = v___y_2111_;
goto v___jp_2097_;
}
}
}
v___jp_2122_:
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_nat_dec_eq(v___y_2125_, v___x_2096_);
if (v___x_2127_ == 0)
{
uint8_t v_trailingOperator_2128_; 
v_trailingOperator_2128_ = lean_ctor_get_uint8(v_format_2045_, 1);
v___y_2110_ = v___y_2123_;
v___y_2111_ = v___y_2126_;
v___y_2112_ = v___x_2127_;
v___y_2113_ = v___y_2124_;
v___y_2114_ = v___y_2125_;
v___y_2115_ = v_trailingOperator_2128_;
goto v___jp_2109_;
}
else
{
lean_object* v___x_2129_; 
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2123_);
v___x_2129_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2));
return v___x_2129_;
}
}
v___jp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v_chain_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2132_ = l_Array_reverse___redArg(v_chain_2091_);
v___x_2133_ = l_Array_popWhile___redArg(v___f_2089_, v___x_2132_);
v_chain_2134_ = l_Array_reverse___redArg(v___x_2133_);
v___x_2135_ = lean_array_get_size(v_chain_2134_);
v___x_2136_ = lean_nat_sub(v_chainSizeBeforePrefixTrim_2092_, v___x_2135_);
v___x_2137_ = lean_nat_mod(v___x_2136_, v___x_2094_);
lean_dec(v___x_2136_);
v___x_2138_ = lean_nat_dec_eq(v___x_2137_, v___x_2096_);
lean_dec(v___x_2137_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; 
v___x_2139_ = 1;
v___y_2123_ = v_chain_2134_;
v___y_2124_ = v___y_2131_;
v___y_2125_ = v___x_2135_;
v___y_2126_ = v___x_2139_;
goto v___jp_2122_;
}
else
{
uint8_t v___x_2140_; 
v___x_2140_ = 0;
v___y_2123_ = v_chain_2134_;
v___y_2124_ = v___y_2131_;
v___y_2125_ = v___x_2135_;
v___y_2126_ = v___x_2140_;
goto v___jp_2122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object* v_format_2144_, lean_object* v_chain_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2144_, v_chain_2145_);
lean_dec_ref(v_format_2144_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object* v___x_2147_, lean_object* v_chain_2148_, lean_object* v_inst_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2147_, v_chain_2148_, v_a_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object* v___x_2152_, lean_object* v_chain_2153_, lean_object* v_inst_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(v___x_2152_, v_chain_2153_, v_inst_2154_, v_a_2155_);
lean_dec_ref(v_chain_2153_);
lean_dec(v___x_2152_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object* v___x_2157_, lean_object* v_chain_2158_, lean_object* v___x_2159_, lean_object* v_inst_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2157_, v_chain_2158_, v___x_2159_, v_a_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object* v___x_2163_, lean_object* v_chain_2164_, lean_object* v___x_2165_, lean_object* v_inst_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(v___x_2163_, v_chain_2164_, v___x_2165_, v_inst_2166_, v_a_2167_);
lean_dec(v___x_2165_);
lean_dec_ref(v_chain_2164_);
lean_dec(v___x_2163_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object* v_chain_2169_, lean_object* v_format_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2203_; 
v_fst_2172_ = lean_ctor_get(v_a_2171_, 0);
v_snd_2173_ = lean_ctor_get(v_a_2171_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_a_2171_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2175_ = v_a_2171_;
v_isShared_2176_ = v_isSharedCheck_2203_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_snd_2173_);
lean_inc(v_fst_2172_);
lean_dec(v_a_2171_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2203_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2177_ = lean_array_get_size(v_chain_2169_);
v___x_2178_ = lean_nat_dec_lt(v_snd_2173_, v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2180_; 
if (v_isShared_2176_ == 0)
{
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_fst_2172_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_snd_2173_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___y_2185_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2182_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2183_ = lean_array_get_borrowed(v___x_2182_, v_chain_2169_, v_snd_2173_);
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_add(v_snd_2173_, v___x_2198_);
v___x_2200_ = lean_nat_dec_lt(v___x_2199_, v___x_2177_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; 
lean_dec(v___x_2199_);
v___x_2201_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2185_ = v___x_2201_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_array_fget_borrowed(v_chain_2169_, v___x_2199_);
lean_dec(v___x_2199_);
lean_inc(v___x_2202_);
v___y_2185_ = v___x_2202_;
goto v___jp_2184_;
}
v___jp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_inc(v___x_2183_);
v___x_2186_ = l_Lean_Fmt_TaggedDoc_nested(v___x_2183_);
v___x_2187_ = lean_unsigned_to_nat(2u);
v___x_2188_ = lean_mk_empty_array_with_capacity(v___x_2187_);
v___x_2189_ = lean_array_push(v___x_2188_, v___x_2186_);
v___x_2190_ = lean_array_push(v___x_2189_, v___y_2185_);
v___x_2191_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2170_, v___x_2190_);
lean_dec_ref(v___x_2190_);
v___x_2192_ = lean_array_push(v_fst_2172_, v___x_2191_);
v___x_2193_ = lean_nat_add(v_snd_2173_, v___x_2187_);
lean_dec(v_snd_2173_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 1, v___x_2193_);
lean_ctor_set(v___x_2175_, 0, v___x_2192_);
v___x_2195_ = v___x_2175_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
v_a_2171_ = v___x_2195_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object* v_chain_2204_, lean_object* v_format_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2204_, v_format_2205_, v_a_2206_);
lean_dec_ref(v_format_2205_);
lean_dec_ref(v_chain_2204_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object* v_chain_2208_, lean_object* v_format_2209_, lean_object* v_a_2210_){
_start:
{
lean_object* v_fst_2211_; lean_object* v_snd_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2242_; 
v_fst_2211_ = lean_ctor_get(v_a_2210_, 0);
v_snd_2212_ = lean_ctor_get(v_a_2210_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2210_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2214_ = v_a_2210_;
v_isShared_2215_ = v_isSharedCheck_2242_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_snd_2212_);
lean_inc(v_fst_2211_);
lean_dec(v_a_2210_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2242_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_array_get_size(v_chain_2208_);
v___x_2217_ = lean_nat_dec_lt(v_snd_2212_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2219_; 
if (v_isShared_2215_ == 0)
{
v___x_2219_ = v___x_2214_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_fst_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_snd_2212_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
else
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___y_2224_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2221_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2222_ = lean_array_get_borrowed(v___x_2221_, v_chain_2208_, v_snd_2212_);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_add(v_snd_2212_, v___x_2237_);
v___x_2239_ = lean_nat_dec_lt(v___x_2238_, v___x_2216_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; 
lean_dec(v___x_2238_);
v___x_2240_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2224_ = v___x_2240_;
goto v___jp_2223_;
}
else
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_array_fget_borrowed(v_chain_2208_, v___x_2238_);
lean_dec(v___x_2238_);
lean_inc(v___x_2241_);
v___y_2224_ = v___x_2241_;
goto v___jp_2223_;
}
v___jp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2225_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2224_);
v___x_2226_ = lean_unsigned_to_nat(2u);
v___x_2227_ = lean_mk_empty_array_with_capacity(v___x_2226_);
lean_inc(v___x_2222_);
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2222_);
v___x_2229_ = lean_array_push(v___x_2228_, v___x_2225_);
v___x_2230_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2209_, v___x_2229_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = lean_array_push(v_fst_2211_, v___x_2230_);
v___x_2232_ = lean_nat_add(v_snd_2212_, v___x_2226_);
lean_dec(v_snd_2212_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2232_);
lean_ctor_set(v___x_2214_, 0, v___x_2231_);
v___x_2234_ = v___x_2214_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v_a_2210_ = v___x_2234_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object* v_chain_2243_, lean_object* v_format_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2243_, v_format_2244_, v_a_2245_);
lean_dec_ref(v_format_2244_);
lean_dec_ref(v_chain_2243_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object* v_format_2247_, lean_object* v_chain_2248_, uint8_t v_isHeadless_2249_){
_start:
{
lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2257_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2267_; uint8_t v___y_2271_; uint8_t v_trailingOperator_2286_; 
v_trailingOperator_2286_ = lean_ctor_get_uint8(v_format_2247_, 1);
v___y_2271_ = v_trailingOperator_2286_;
goto v___jp_2270_;
v___jp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_fst_2255_; 
v___x_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___y_2251_);
lean_ctor_set(v___x_2253_, 1, v___y_2252_);
v___x_2254_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2248_, v_format_2247_, v___x_2253_);
v_fst_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_fst_2255_);
lean_dec_ref(v___x_2254_);
return v_fst_2255_;
}
v___jp_2256_:
{
if (v_isHeadless_2249_ == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_unsigned_to_nat(1u);
v___y_2251_ = v___y_2257_;
v___y_2252_ = v___x_2258_;
goto v___jp_2250_;
}
else
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_unsigned_to_nat(0u);
v___y_2251_ = v___y_2257_;
v___y_2252_ = v___x_2259_;
goto v___jp_2250_;
}
}
v___jp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_fst_2265_; 
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___y_2261_);
lean_ctor_set(v___x_2263_, 1, v___y_2262_);
v___x_2264_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2248_, v_format_2247_, v___x_2263_);
v_fst_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_fst_2265_);
lean_dec_ref(v___x_2264_);
return v_fst_2265_;
}
v___jp_2266_:
{
if (v_isHeadless_2249_ == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_unsigned_to_nat(0u);
v___y_2261_ = v___y_2267_;
v___y_2262_ = v___x_2268_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2269_; 
v___x_2269_ = lean_unsigned_to_nat(1u);
v___y_2261_ = v___y_2267_;
v___y_2262_ = v___x_2269_;
goto v___jp_2260_;
}
}
v___jp_2270_:
{
if (v___y_2271_ == 0)
{
if (v_isHeadless_2249_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2272_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_array_get_borrowed(v___x_2272_, v_chain_2248_, v___x_2273_);
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = lean_mk_empty_array_with_capacity(v___x_2275_);
lean_inc(v___x_2274_);
v___x_2277_ = lean_array_push(v___x_2276_, v___x_2274_);
v___y_2257_ = v___x_2277_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2278_; 
v___x_2278_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2257_ = v___x_2278_;
goto v___jp_2256_;
}
}
else
{
if (v_isHeadless_2249_ == 0)
{
lean_object* v___x_2279_; 
v___x_2279_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2267_ = v___x_2279_;
goto v___jp_2266_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2280_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = lean_array_get_borrowed(v___x_2280_, v_chain_2248_, v___x_2281_);
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_mk_empty_array_with_capacity(v___x_2283_);
lean_inc(v___x_2282_);
v___x_2285_ = lean_array_push(v___x_2284_, v___x_2282_);
v___y_2267_ = v___x_2285_;
goto v___jp_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object* v_format_2287_, lean_object* v_chain_2288_, lean_object* v_isHeadless_2289_){
_start:
{
uint8_t v_isHeadless_boxed_2290_; lean_object* v_res_2291_; 
v_isHeadless_boxed_2290_ = lean_unbox(v_isHeadless_2289_);
v_res_2291_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2287_, v_chain_2288_, v_isHeadless_boxed_2290_);
lean_dec_ref(v_chain_2288_);
lean_dec_ref(v_format_2287_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object* v_chain_2292_, lean_object* v_format_2293_, lean_object* v_inst_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2292_, v_format_2293_, v_a_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object* v_chain_2297_, lean_object* v_format_2298_, lean_object* v_inst_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(v_chain_2297_, v_format_2298_, v_inst_2299_, v_a_2300_);
lean_dec_ref(v_format_2298_);
lean_dec_ref(v_chain_2297_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object* v_chain_2302_, lean_object* v_format_2303_, lean_object* v_inst_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2302_, v_format_2303_, v_a_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object* v_chain_2307_, lean_object* v_format_2308_, lean_object* v_inst_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(v_chain_2307_, v_format_2308_, v_inst_2309_, v_a_2310_);
lean_dec_ref(v_format_2308_);
lean_dec_ref(v_chain_2307_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object* v_format_2312_, lean_object* v_docs_2313_){
_start:
{
uint8_t v___y_2315_; uint8_t v_spacing_2318_; 
v_spacing_2318_ = lean_ctor_get_uint8(v_format_2312_, 2);
v___y_2315_ = v_spacing_2318_;
goto v___jp_2314_;
v___jp_2314_:
{
if (v___y_2315_ == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Fmt_TaggedDoc_fill(v_docs_2313_);
return v___x_2316_;
}
else
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v_docs_2313_);
return v___x_2317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object* v_format_2319_, lean_object* v_docs_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2319_, v_docs_2320_);
lean_dec_ref(v_format_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object* v_columnPos_2322_, lean_object* v_indentation_2323_, lean_object* v_nonCumulativeIndentation_2324_){
_start:
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = lean_nat_add(v_indentation_2323_, v_nonCumulativeIndentation_2324_);
v___x_2326_ = lean_nat_dec_le(v_columnPos_2322_, v___x_2325_);
lean_dec(v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object* v_columnPos_2327_, lean_object* v_indentation_2328_, lean_object* v_nonCumulativeIndentation_2329_){
_start:
{
uint8_t v_res_2330_; lean_object* v_r_2331_; 
v_res_2330_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(v_columnPos_2327_, v_indentation_2328_, v_nonCumulativeIndentation_2329_);
lean_dec(v_nonCumulativeIndentation_2329_);
lean_dec(v_indentation_2328_);
lean_dec(v_columnPos_2327_);
v_r_2331_ = lean_box(v_res_2330_);
return v_r_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object* v_format_2348_, lean_object* v_combinedChain_2349_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v_firstOperand_2352_; lean_object* v___y_2354_; uint8_t v___y_2375_; uint8_t v_hardNestedFirstOperand_2382_; 
v___x_2350_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2351_ = lean_unsigned_to_nat(0u);
v_firstOperand_2352_ = lean_array_get_borrowed(v___x_2350_, v_combinedChain_2349_, v___x_2351_);
v_hardNestedFirstOperand_2382_ = lean_ctor_get_uint8(v_format_2348_, 0);
v___y_2375_ = v_hardNestedFirstOperand_2382_;
goto v___jp_2374_;
v___jp_2353_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_compactFirstOperation_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v_compactedChain_2369_; lean_object* v___x_2370_; 
lean_inc(v_firstOperand_2352_);
v___x_2355_ = l_Lean_Fmt_TaggedDoc_flattened(v_firstOperand_2352_);
v___x_2356_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion));
v___x_2357_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2356_, v___y_2354_);
v___x_2358_ = lean_unsigned_to_nat(2u);
v___x_2359_ = lean_mk_empty_array_with_capacity(v___x_2358_);
v___x_2360_ = lean_array_push(v___x_2359_, v___x_2355_);
v___x_2361_ = lean_array_push(v___x_2360_, v___x_2357_);
v_compactFirstOperation_2362_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2348_, v___x_2361_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_mk_empty_array_with_capacity(v___x_2363_);
v___x_2365_ = lean_array_push(v___x_2364_, v_compactFirstOperation_2362_);
v___x_2366_ = lean_array_get_size(v_combinedChain_2349_);
v___x_2367_ = l_Array_toSubarray___redArg(v_combinedChain_2349_, v___x_2358_, v___x_2366_);
v___x_2368_ = l_Subarray_copy___redArg(v___x_2367_);
v_compactedChain_2369_ = l_Array_append___redArg(v___x_2365_, v___x_2368_);
lean_dec_ref(v___x_2368_);
v___x_2370_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2348_, v_compactedChain_2369_);
return v___x_2370_;
}
v___jp_2371_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = lean_array_get_borrowed(v___x_2350_, v_combinedChain_2349_, v___x_2372_);
lean_inc(v___x_2373_);
v___y_2354_ = v___x_2373_;
goto v___jp_2353_;
}
v___jp_2374_:
{
if (v___y_2375_ == 0)
{
goto v___jp_2371_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2376_ = lean_unsigned_to_nat(2u);
v___x_2377_ = lean_array_get_size(v_combinedChain_2349_);
v___x_2378_ = lean_nat_dec_lt(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
goto v___jp_2371_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2379_ = lean_unsigned_to_nat(1u);
v___x_2380_ = lean_array_get_borrowed(v___x_2350_, v_combinedChain_2349_, v___x_2379_);
lean_inc(v___x_2380_);
v___x_2381_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2380_);
v___y_2354_ = v___x_2381_;
goto v___jp_2353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object* v_format_2383_, lean_object* v_combinedChain_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2383_, v_combinedChain_2384_);
lean_dec_ref(v_format_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object* v_format_2386_, lean_object* v_docs_2387_, lean_object* v_wrap_2388_){
_start:
{
uint8_t v___y_2390_; uint8_t v_spacing_2393_; 
v_spacing_2393_ = lean_ctor_get_uint8(v_format_2386_, 2);
v___y_2390_ = v_spacing_2393_;
goto v___jp_2389_;
v___jp_2389_:
{
if (v___y_2390_ == 0)
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_Fmt_TaggedDoc_fillWrapping(v_docs_2387_, v_wrap_2388_);
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(v_docs_2387_, v_wrap_2388_);
return v___x_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object* v_format_2394_, lean_object* v_docs_2395_, lean_object* v_wrap_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2394_, v_docs_2395_, v_wrap_2396_);
lean_dec_ref(v_format_2394_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object* v___x_2398_, size_t v_sz_2399_, size_t v_i_2400_, lean_object* v_bs_2401_){
_start:
{
uint8_t v___x_2402_; 
v___x_2402_ = lean_usize_dec_lt(v_i_2400_, v_sz_2399_);
if (v___x_2402_ == 0)
{
return v_bs_2401_;
}
else
{
lean_object* v___x_2403_; lean_object* v_v_2404_; lean_object* v___x_2405_; lean_object* v_bs_x27_2406_; lean_object* v___y_2408_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2403_ = lean_unsigned_to_nat(1u);
v_v_2404_ = lean_array_uget(v_bs_2401_, v_i_2400_);
v___x_2405_ = lean_unsigned_to_nat(0u);
v_bs_x27_2406_ = lean_array_uset(v_bs_2401_, v_i_2400_, v___x_2405_);
v___x_2413_ = lean_usize_to_nat(v_i_2400_);
v___x_2414_ = lean_nat_sub(v___x_2398_, v___x_2403_);
v___x_2415_ = lean_nat_dec_lt(v___x_2413_, v___x_2414_);
lean_dec(v___x_2414_);
lean_dec(v___x_2413_);
if (v___x_2415_ == 0)
{
v___y_2408_ = v_v_2404_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2404_);
v___y_2408_ = v___x_2416_;
goto v___jp_2407_;
}
v___jp_2407_:
{
size_t v___x_2409_; size_t v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = ((size_t)1ULL);
v___x_2410_ = lean_usize_add(v_i_2400_, v___x_2409_);
v___x_2411_ = lean_array_uset(v_bs_x27_2406_, v_i_2400_, v___y_2408_);
v_i_2400_ = v___x_2410_;
v_bs_2401_ = v___x_2411_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object* v___x_2417_, lean_object* v_sz_2418_, lean_object* v_i_2419_, lean_object* v_bs_2420_){
_start:
{
size_t v_sz_boxed_2421_; size_t v_i_boxed_2422_; lean_object* v_res_2423_; 
v_sz_boxed_2421_ = lean_unbox_usize(v_sz_2418_);
lean_dec(v_sz_2418_);
v_i_boxed_2422_ = lean_unbox_usize(v_i_2419_);
lean_dec(v_i_2419_);
v_res_2423_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2417_, v_sz_boxed_2421_, v_i_boxed_2422_, v_bs_2420_);
lean_dec(v___x_2417_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object* v_chain_2438_, lean_object* v_format_2439_){
_start:
{
uint8_t v___y_2441_; lean_object* v_doc_2442_; lean_object* v___x_2446_; lean_object* v_snd_2447_; lean_object* v_fst_2448_; lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___x_2453_; 
v___x_2446_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2439_, v_chain_2438_);
v_snd_2447_ = lean_ctor_get(v___x_2446_, 1);
lean_inc(v_snd_2447_);
v_fst_2448_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_fst_2448_);
lean_dec_ref(v___x_2446_);
v_fst_2449_ = lean_ctor_get(v_snd_2447_, 0);
lean_inc(v_fst_2449_);
v_snd_2450_ = lean_ctor_get(v_snd_2447_, 1);
lean_inc(v_snd_2450_);
lean_dec(v_snd_2447_);
v___x_2451_ = lean_array_get_size(v_fst_2448_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_nat_dec_eq(v___x_2451_, v___x_2452_);
if (v___x_2453_ == 0)
{
uint8_t v___x_2454_; lean_object* v_combinedChain_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___y_2459_; lean_object* v___y_2460_; lean_object* v_doc_2461_; uint8_t v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; uint8_t v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v_combinedChain_2502_; uint8_t v___y_2505_; uint8_t v___y_2512_; uint8_t v___y_2513_; uint8_t v___y_2521_; uint8_t v___y_2524_; uint8_t v___x_2525_; 
v___x_2454_ = lean_unbox(v_fst_2449_);
v_combinedChain_2455_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2439_, v_fst_2448_, v___x_2454_);
v___x_2456_ = lean_array_get_size(v_combinedChain_2455_);
v___x_2457_ = lean_unsigned_to_nat(1u);
v___x_2525_ = lean_nat_dec_eq(v___x_2456_, v___x_2457_);
if (v___x_2525_ == 0)
{
uint8_t v_trailingOperator_2526_; 
v_trailingOperator_2526_ = lean_ctor_get_uint8(v_format_2439_, 1);
v___y_2524_ = v_trailingOperator_2526_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec(v_snd_2450_);
lean_dec(v_fst_2449_);
lean_dec(v_fst_2448_);
v___x_2527_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2528_ = lean_array_get(v___x_2527_, v_combinedChain_2455_, v___x_2452_);
lean_dec_ref(v_combinedChain_2455_);
return v___x_2528_;
}
v___jp_2458_:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v_lastOperand_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; lean_object* v___x_2467_; 
v___x_2462_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2463_ = lean_nat_sub(v___x_2451_, v___x_2457_);
v_lastOperand_2464_ = lean_array_get(v___x_2462_, v_fst_2448_, v___x_2463_);
lean_dec(v___x_2463_);
lean_dec(v_fst_2448_);
v___x_2465_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
v___x_2466_ = lean_unbox(v_snd_2450_);
lean_inc_ref(v___y_2460_);
lean_inc(v_lastOperand_2464_);
lean_inc_ref(v_doc_2461_);
v___x_2467_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2439_, v_doc_2461_, v_lastOperand_2464_, v___x_2466_, v___y_2460_, v___x_2465_);
if (lean_obj_tag(v___x_2467_) == 1)
{
lean_object* v_val_2468_; 
lean_dec(v_lastOperand_2464_);
lean_dec_ref(v_doc_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v_snd_2450_);
v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___y_2441_ = v___y_2459_;
v_doc_2442_ = v_val_2468_;
goto v___jp_2440_;
}
else
{
uint8_t v___x_2469_; lean_object* v___x_2470_; 
lean_dec(v___x_2467_);
v___x_2469_ = lean_unbox(v_snd_2450_);
lean_inc_ref(v___y_2460_);
lean_inc(v_lastOperand_2464_);
lean_inc_ref(v_doc_2461_);
v___x_2470_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2439_, v_doc_2461_, v_lastOperand_2464_, v___x_2469_, v___y_2460_);
if (lean_obj_tag(v___x_2470_) == 1)
{
lean_object* v_val_2471_; 
lean_dec(v_lastOperand_2464_);
lean_dec_ref(v_doc_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v_snd_2450_);
v_val_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___y_2441_ = v___y_2459_;
v_doc_2442_ = v_val_2471_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; 
lean_dec(v___x_2470_);
v___x_2472_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
v___x_2473_ = lean_unbox(v_snd_2450_);
lean_dec(v_snd_2450_);
lean_inc_ref(v_doc_2461_);
v___x_2474_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2439_, v_doc_2461_, v_lastOperand_2464_, v___x_2473_, v___y_2460_, v___x_2472_);
if (lean_obj_tag(v___x_2474_) == 1)
{
lean_object* v_val_2475_; 
lean_dec_ref(v_doc_2461_);
v_val_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_val_2475_);
lean_dec_ref_known(v___x_2474_, 1);
v___y_2441_ = v___y_2459_;
v_doc_2442_ = v_val_2475_;
goto v___jp_2440_;
}
else
{
lean_dec(v___x_2474_);
v___y_2441_ = v___y_2459_;
v_doc_2442_ = v_doc_2461_;
goto v___jp_2440_;
}
}
}
}
v___jp_2476_:
{
if (v___y_2477_ == 0)
{
v___y_2459_ = v___y_2477_;
v___y_2460_ = v___y_2478_;
v_doc_2461_ = v___y_2479_;
goto v___jp_2458_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_doc_2485_; 
lean_inc_ref(v___y_2478_);
v___x_2480_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2439_, v___y_2478_);
v___x_2481_ = lean_unsigned_to_nat(2u);
v___x_2482_ = lean_mk_empty_array_with_capacity(v___x_2481_);
v___x_2483_ = lean_array_push(v___x_2482_, v___x_2480_);
v___x_2484_ = lean_array_push(v___x_2483_, v___y_2479_);
v_doc_2485_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2484_);
v___y_2459_ = v___y_2477_;
v___y_2460_ = v___y_2478_;
v_doc_2461_ = v_doc_2485_;
goto v___jp_2458_;
}
}
v___jp_2486_:
{
uint8_t v___x_2490_; 
v___x_2490_ = lean_unbox(v_fst_2449_);
lean_dec(v_fst_2449_);
if (v___x_2490_ == 0)
{
v___y_2477_ = v___y_2487_;
v___y_2478_ = v___y_2488_;
v___y_2479_ = v___y_2489_;
goto v___jp_2476_;
}
else
{
if (v___x_2453_ == 0)
{
v___y_2459_ = v___y_2487_;
v___y_2460_ = v___y_2488_;
v_doc_2461_ = v___y_2489_;
goto v___jp_2458_;
}
else
{
v___y_2477_ = v___y_2487_;
v___y_2478_ = v___y_2488_;
v___y_2479_ = v___y_2489_;
goto v___jp_2476_;
}
}
}
v___jp_2491_:
{
lean_object* v___x_2494_; 
lean_inc_ref(v___y_2492_);
v___x_2494_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2439_, v___y_2492_);
v___y_2487_ = v___y_2493_;
v___y_2488_ = v___y_2492_;
v___y_2489_ = v___x_2494_;
goto v___jp_2486_;
}
v___jp_2495_:
{
if (v___y_2497_ == 0)
{
uint8_t v___x_2498_; 
v___x_2498_ = 1;
v___y_2492_ = v___y_2496_;
v___y_2493_ = v___x_2498_;
goto v___jp_2491_;
}
else
{
if (v___x_2453_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
lean_inc_ref(v___y_2496_);
v___x_2500_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2439_, v___y_2496_, v___x_2499_);
v___y_2487_ = v___x_2453_;
v___y_2488_ = v___y_2496_;
v___y_2489_ = v___x_2500_;
goto v___jp_2486_;
}
else
{
v___y_2492_ = v___y_2496_;
v___y_2493_ = v___x_2453_;
goto v___jp_2491_;
}
}
}
v___jp_2501_:
{
uint8_t v_trailingOperator_2503_; 
v_trailingOperator_2503_ = lean_ctor_get_uint8(v_format_2439_, 1);
v___y_2496_ = v_combinedChain_2502_;
v___y_2497_ = v_trailingOperator_2503_;
goto v___jp_2495_;
}
v___jp_2504_:
{
if (v___y_2505_ == 0)
{
v_combinedChain_2502_ = v_combinedChain_2455_;
goto v___jp_2501_;
}
else
{
size_t v_sz_2506_; size_t v___x_2507_; lean_object* v_combinedChain_2508_; 
v_sz_2506_ = lean_array_size(v_combinedChain_2455_);
v___x_2507_ = ((size_t)0ULL);
v_combinedChain_2508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2456_, v_sz_2506_, v___x_2507_, v_combinedChain_2455_);
v_combinedChain_2502_ = v_combinedChain_2508_;
goto v___jp_2501_;
}
}
v___jp_2509_:
{
uint8_t v_hardNestedFirstOperand_2510_; 
v_hardNestedFirstOperand_2510_ = lean_ctor_get_uint8(v_format_2439_, 0);
v___y_2505_ = v_hardNestedFirstOperand_2510_;
goto v___jp_2504_;
}
v___jp_2511_:
{
if (v___y_2513_ == 0)
{
if (v___y_2512_ == 0)
{
v_combinedChain_2502_ = v_combinedChain_2455_;
goto v___jp_2501_;
}
else
{
goto v___jp_2509_;
}
}
else
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_nat_dec_lt(v___x_2452_, v___x_2456_);
if (v___x_2514_ == 0)
{
v_combinedChain_2502_ = v_combinedChain_2455_;
goto v___jp_2501_;
}
else
{
lean_object* v_v_2515_; lean_object* v___x_2516_; lean_object* v_xs_x27_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_v_2515_ = lean_array_fget(v_combinedChain_2455_, v___x_2452_);
v___x_2516_ = lean_box(0);
v_xs_x27_2517_ = lean_array_fset(v_combinedChain_2455_, v___x_2452_, v___x_2516_);
v___x_2518_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2515_);
v___x_2519_ = lean_array_fset(v_xs_x27_2517_, v___x_2452_, v___x_2518_);
v_combinedChain_2502_ = v___x_2519_;
goto v___jp_2501_;
}
}
}
v___jp_2520_:
{
uint8_t v_hardNestedFirstOperand_2522_; 
v_hardNestedFirstOperand_2522_ = lean_ctor_get_uint8(v_format_2439_, 0);
v___y_2512_ = v___y_2521_;
v___y_2513_ = v_hardNestedFirstOperand_2522_;
goto v___jp_2511_;
}
v___jp_2523_:
{
if (v___y_2524_ == 0)
{
v___y_2521_ = v___y_2524_;
goto v___jp_2520_;
}
else
{
if (v___x_2453_ == 0)
{
goto v___jp_2509_;
}
else
{
v___y_2521_ = v___y_2524_;
goto v___jp_2520_;
}
}
}
}
else
{
lean_object* v___x_2529_; 
lean_dec(v_snd_2450_);
lean_dec(v_fst_2449_);
lean_dec(v_fst_2448_);
v___x_2529_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_2529_;
}
v___jp_2440_:
{
if (v___y_2441_ == 0)
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2442_);
return v___x_2443_;
}
else
{
lean_object* v_doc_2444_; lean_object* v___x_2445_; 
v_doc_2444_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2442_);
v___x_2445_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2444_);
return v___x_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object* v_chain_2530_, lean_object* v_format_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_2530_, v_format_2531_);
lean_dec_ref(v_format_2531_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object* v___x_2533_, lean_object* v_as_2534_, size_t v_sz_2535_, size_t v_i_2536_, lean_object* v_bs_2537_){
_start:
{
lean_object* v___x_2538_; 
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2533_, v_sz_2535_, v_i_2536_, v_bs_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object* v___x_2539_, lean_object* v_as_2540_, lean_object* v_sz_2541_, lean_object* v_i_2542_, lean_object* v_bs_2543_){
_start:
{
size_t v_sz_boxed_2544_; size_t v_i_boxed_2545_; lean_object* v_res_2546_; 
v_sz_boxed_2544_ = lean_unbox_usize(v_sz_2541_);
lean_dec(v_sz_2541_);
v_i_boxed_2545_ = lean_unbox_usize(v_i_2542_);
lean_dec(v_i_2542_);
v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(v___x_2539_, v_as_2540_, v_sz_boxed_2544_, v_i_boxed_2545_, v_bs_2543_);
lean_dec_ref(v_as_2540_);
lean_dec(v___x_2539_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object* v_lhs_2547_, lean_object* v_typeAscriptionTk_2548_, lean_object* v_rhs_2549_, lean_object* v_format_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2551_ = lean_unsigned_to_nat(3u);
v___x_2552_ = lean_mk_empty_array_with_capacity(v___x_2551_);
v___x_2553_ = lean_array_push(v___x_2552_, v_lhs_2547_);
v___x_2554_ = lean_array_push(v___x_2553_, v_typeAscriptionTk_2548_);
v___x_2555_ = lean_array_push(v___x_2554_, v_rhs_2549_);
v___x_2556_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2555_, v_format_2550_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object* v_lhs_2557_, lean_object* v_typeAscriptionTk_2558_, lean_object* v_rhs_2559_, lean_object* v_format_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Fmt_Layouts_typeAscription(v_lhs_2557_, v_typeAscriptionTk_2558_, v_rhs_2559_, v_format_2560_);
lean_dec_ref(v_format_2560_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(lean_object* v_x_2562_){
_start:
{
if (lean_obj_tag(v_x_2562_) == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_unsigned_to_nat(0u);
return v___x_2563_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_unsigned_to_nat(1u);
return v___x_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___boxed(lean_object* v_x_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(v_x_2565_);
lean_dec_ref(v_x_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object* v_t_2567_, lean_object* v_k_2568_){
_start:
{
if (lean_obj_tag(v_t_2567_) == 0)
{
uint8_t v_spacing_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_spacing_2569_ = lean_ctor_get_uint8(v_t_2567_, 0);
lean_dec_ref_known(v_t_2567_, 0);
v___x_2570_ = lean_box(v_spacing_2569_);
v___x_2571_ = lean_apply_1(v_k_2568_, v___x_2570_);
return v___x_2571_;
}
else
{
lean_object* v_sep_2572_; uint8_t v_unindentedRb_2573_; uint8_t v_stickynessKind_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v_sep_2572_ = lean_ctor_get(v_t_2567_, 0);
lean_inc_ref(v_sep_2572_);
v_unindentedRb_2573_ = lean_ctor_get_uint8(v_t_2567_, sizeof(void*)*1);
v_stickynessKind_2574_ = lean_ctor_get_uint8(v_t_2567_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_2567_, 1);
v___x_2575_ = lean_box(v_unindentedRb_2573_);
v___x_2576_ = lean_box(v_stickynessKind_2574_);
v___x_2577_ = lean_apply_3(v_k_2568_, v_sep_2572_, v___x_2575_, v___x_2576_);
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object* v_motive_2578_, lean_object* v_ctorIdx_2579_, lean_object* v_t_2580_, lean_object* v_h_2581_, lean_object* v_k_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2580_, v_k_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object* v_motive_2584_, lean_object* v_ctorIdx_2585_, lean_object* v_t_2586_, lean_object* v_h_2587_, lean_object* v_k_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(v_motive_2584_, v_ctorIdx_2585_, v_t_2586_, v_h_2587_, v_k_2588_);
lean_dec(v_ctorIdx_2585_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object* v_t_2590_, lean_object* v_dense_2591_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2590_, v_dense_2591_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object* v_motive_2593_, lean_object* v_t_2594_, lean_object* v_h_2595_, lean_object* v_dense_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2594_, v_dense_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object* v_t_2598_, lean_object* v_sparse_2599_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2598_, v_sparse_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object* v_motive_2601_, lean_object* v_t_2602_, lean_object* v_h_2603_, lean_object* v_sparse_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2602_, v_sparse_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object* v_lb_2606_, lean_object* v_rb_2607_, uint8_t v_isBodyAligned_2608_, uint8_t v_isBodyPseudoAligned_2609_, uint8_t v___x_2610_, lean_object* v_body_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_doc_2618_; 
v___x_2612_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2611_);
v___x_2613_ = lean_unsigned_to_nat(3u);
v___x_2614_ = lean_mk_empty_array_with_capacity(v___x_2613_);
v___x_2615_ = lean_array_push(v___x_2614_, v_lb_2606_);
v___x_2616_ = lean_array_push(v___x_2615_, v___x_2612_);
v___x_2617_ = lean_array_push(v___x_2616_, v_rb_2607_);
v_doc_2618_ = l_Lean_Fmt_Layouts_atomic(v___x_2617_);
lean_dec_ref(v___x_2617_);
if (v_isBodyAligned_2608_ == 0)
{
if (v_isBodyPseudoAligned_2609_ == 0)
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2618_, v___x_2610_);
return v___x_2619_;
}
else
{
lean_object* v_doc_2620_; lean_object* v___x_2621_; 
v_doc_2620_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2618_);
v___x_2621_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2620_, v___x_2610_);
return v___x_2621_;
}
}
else
{
lean_object* v_doc_2622_; lean_object* v___x_2623_; 
v_doc_2622_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_2618_);
v___x_2623_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2622_, v___x_2610_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object* v_lb_2624_, lean_object* v_rb_2625_, lean_object* v_isBodyAligned_2626_, lean_object* v_isBodyPseudoAligned_2627_, lean_object* v___x_2628_, lean_object* v_body_2629_){
_start:
{
uint8_t v_isBodyAligned_boxed_2630_; uint8_t v_isBodyPseudoAligned_boxed_2631_; uint8_t v___x_901__boxed_2632_; lean_object* v_res_2633_; 
v_isBodyAligned_boxed_2630_ = lean_unbox(v_isBodyAligned_2626_);
v_isBodyPseudoAligned_boxed_2631_ = lean_unbox(v_isBodyPseudoAligned_2627_);
v___x_901__boxed_2632_ = lean_unbox(v___x_2628_);
v_res_2633_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2624_, v_rb_2625_, v_isBodyAligned_boxed_2630_, v_isBodyPseudoAligned_boxed_2631_, v___x_901__boxed_2632_, v_body_2629_);
return v_res_2633_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_bracketed___lam__1(uint8_t v_unindentedRb_2634_, lean_object* v_columnPos_2635_, lean_object* v_indentation_2636_, lean_object* v_nonCumulativeIndentation_2637_){
_start:
{
if (v_unindentedRb_2634_ == 0)
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = lean_nat_add(v_indentation_2636_, v_nonCumulativeIndentation_2637_);
v___x_2639_ = lean_nat_dec_lt(v_columnPos_2635_, v___x_2638_);
lean_dec(v___x_2638_);
return v___x_2639_;
}
else
{
uint8_t v___x_2640_; 
v___x_2640_ = lean_nat_dec_lt(v_columnPos_2635_, v_indentation_2636_);
return v___x_2640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__1___boxed(lean_object* v_unindentedRb_2641_, lean_object* v_columnPos_2642_, lean_object* v_indentation_2643_, lean_object* v_nonCumulativeIndentation_2644_){
_start:
{
uint8_t v_unindentedRb_922__boxed_2645_; uint8_t v_res_2646_; lean_object* v_r_2647_; 
v_unindentedRb_922__boxed_2645_ = lean_unbox(v_unindentedRb_2641_);
v_res_2646_ = l_Lean_Fmt_Layouts_bracketed___lam__1(v_unindentedRb_922__boxed_2645_, v_columnPos_2642_, v_indentation_2643_, v_nonCumulativeIndentation_2644_);
lean_dec(v_nonCumulativeIndentation_2644_);
lean_dec(v_indentation_2643_);
lean_dec(v_columnPos_2642_);
v_r_2647_ = lean_box(v_res_2646_);
return v_r_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object* v_lb_2657_, lean_object* v_body_2658_, lean_object* v_rb_2659_, lean_object* v_format_2660_){
_start:
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2658_);
if (v___x_2661_ == 0)
{
lean_object* v_doc_2662_; uint8_t v___x_2663_; 
v_doc_2662_ = lean_ctor_get(v_body_2658_, 0);
v___x_2663_ = 1;
if (lean_obj_tag(v_format_2660_) == 0)
{
uint8_t v_spacing_2664_; 
v_spacing_2664_ = lean_ctor_get_uint8(v_format_2660_, 0);
lean_dec_ref_known(v_format_2660_, 0);
if (v_spacing_2664_ == 0)
{
uint8_t v_isBodyAligned_2665_; uint8_t v_isBodyPseudoAligned_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v_f_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_inc(v_doc_2662_);
v_isBodyAligned_2665_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2662_);
lean_inc_ref(v_body_2658_);
v_isBodyPseudoAligned_2666_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_body_2658_);
v___x_2667_ = lean_box(v_isBodyAligned_2665_);
v___x_2668_ = lean_box(v_isBodyPseudoAligned_2666_);
v___x_2669_ = lean_box(v___x_2663_);
v_f_2670_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__0___boxed), 6, 5);
lean_closure_set(v_f_2670_, 0, v_lb_2657_);
lean_closure_set(v_f_2670_, 1, v_rb_2659_);
lean_closure_set(v_f_2670_, 2, v___x_2667_);
lean_closure_set(v_f_2670_, 3, v___x_2668_);
lean_closure_set(v_f_2670_, 4, v___x_2669_);
v___x_2671_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__0));
v___x_2672_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_body_2658_, v_f_2670_, v___x_2671_);
return v___x_2672_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2673_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2658_);
v___x_2674_ = lean_unsigned_to_nat(3u);
v___x_2675_ = lean_mk_empty_array_with_capacity(v___x_2674_);
v___x_2676_ = lean_array_push(v___x_2675_, v_lb_2657_);
v___x_2677_ = lean_array_push(v___x_2676_, v___x_2673_);
v___x_2678_ = lean_array_push(v___x_2677_, v_rb_2659_);
v___x_2679_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2678_);
lean_dec_ref(v___x_2678_);
return v___x_2679_;
}
}
else
{
lean_object* v_sep_2680_; uint8_t v_unindentedRb_2681_; uint8_t v_stickynessKind_2682_; lean_object* v___x_2683_; lean_object* v_denseAssertion_2684_; lean_object* v_body_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v_dense_2694_; lean_object* v_sparse_2696_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v_sparse_2712_; 
v_sep_2680_ = lean_ctor_get(v_format_2660_, 0);
lean_inc_ref_n(v_sep_2680_, 3);
v_unindentedRb_2681_ = lean_ctor_get_uint8(v_format_2660_, sizeof(void*)*1);
v_stickynessKind_2682_ = lean_ctor_get_uint8(v_format_2660_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_format_2660_, 1);
v___x_2683_ = lean_box(v_unindentedRb_2681_);
v_denseAssertion_2684_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__1___boxed), 4, 1);
lean_closure_set(v_denseAssertion_2684_, 0, v___x_2683_);
v_body_2685_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_2658_);
v___x_2686_ = l_Lean_Fmt_TaggedDoc_flattened(v_sep_2680_);
v___x_2687_ = lean_unsigned_to_nat(5u);
v___x_2688_ = lean_mk_empty_array_with_capacity(v___x_2687_);
lean_inc_ref(v_lb_2657_);
v___x_2689_ = lean_array_push(v___x_2688_, v_lb_2657_);
lean_inc_ref(v___x_2686_);
v___x_2690_ = lean_array_push(v___x_2689_, v___x_2686_);
lean_inc_ref(v_body_2685_);
v___x_2691_ = lean_array_push(v___x_2690_, v_body_2685_);
v___x_2692_ = lean_array_push(v___x_2691_, v___x_2686_);
lean_inc_ref(v_rb_2659_);
v___x_2693_ = lean_array_push(v___x_2692_, v_rb_2659_);
v_dense_2694_ = l_Lean_Fmt_Layouts_atomic(v___x_2693_);
lean_dec_ref(v___x_2693_);
v___x_2708_ = l_Lean_Fmt_TaggedDoc_append(v_sep_2680_, v_body_2685_);
v___x_2709_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2708_);
v___x_2710_ = l_Lean_Fmt_TaggedDoc_append(v_lb_2657_, v___x_2709_);
v___x_2711_ = l_Lean_Fmt_TaggedDoc_append(v___x_2710_, v_sep_2680_);
v_sparse_2712_ = l_Lean_Fmt_TaggedDoc_append(v___x_2711_, v_rb_2659_);
if (v_unindentedRb_2681_ == 0)
{
v_sparse_2696_ = v_sparse_2712_;
goto v___jp_2695_;
}
else
{
lean_object* v_sparse_2713_; 
v_sparse_2713_ = l_Lean_Fmt_TaggedDoc_unindented(v_sparse_2712_, v___x_2663_);
v_sparse_2696_ = v_sparse_2713_;
goto v___jp_2695_;
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v_stickyVariant_2705_; lean_object* v_nonStickyVariant_2706_; lean_object* v___x_2707_; 
v___x_2697_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__2));
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_denseAssertion_2684_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2698_, v_dense_2694_);
v___x_2700_ = lean_unsigned_to_nat(2u);
v___x_2701_ = lean_mk_empty_array_with_capacity(v___x_2700_);
v___x_2702_ = lean_array_push(v___x_2701_, v___x_2699_);
v___x_2703_ = lean_array_push(v___x_2702_, v_sparse_2696_);
v___x_2704_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2703_);
v_stickyVariant_2705_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_2704_, v___x_2663_);
lean_inc_ref(v_stickyVariant_2705_);
v_nonStickyVariant_2706_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_stickyVariant_2705_);
v___x_2707_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_2706_, v_stickyVariant_2705_, v_stickynessKind_2682_);
return v___x_2707_;
}
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec_ref(v_format_2660_);
lean_dec_ref(v_body_2658_);
v___x_2714_ = lean_unsigned_to_nat(2u);
v___x_2715_ = lean_mk_empty_array_with_capacity(v___x_2714_);
v___x_2716_ = lean_array_push(v___x_2715_, v_lb_2657_);
v___x_2717_ = lean_array_push(v___x_2716_, v_rb_2659_);
v___x_2718_ = l_Lean_Fmt_Layouts_atomic(v___x_2717_);
lean_dec_ref(v___x_2717_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object* v_lbTk_2721_, lean_object* v_body_2722_, lean_object* v_rbTk_2723_){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_2725_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2721_, v_body_2722_, v_rbTk_2723_, v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0(void){
_start:
{
uint8_t v___x_2726_; uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2726_ = 1;
v___x_2727_ = 1;
v___x_2728_ = l_Lean_Fmt_TaggedDoc_break;
v___x_2729_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1, v___x_2727_);
lean_ctor_set_uint8(v___x_2729_, sizeof(void*)*1 + 1, v___x_2726_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object* v_lbTk_2730_, lean_object* v_seq_2731_, lean_object* v_rbTk_2732_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_obj_once(&l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0, &l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0);
v___x_2734_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_2730_, v_seq_2731_, v_rbTk_2732_, v___x_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t v_sz_2735_, size_t v_i_2736_, lean_object* v_bs_2737_){
_start:
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_usize_dec_lt(v_i_2736_, v_sz_2735_);
if (v___x_2738_ == 0)
{
return v_bs_2737_;
}
else
{
lean_object* v_v_2739_; lean_object* v___x_2740_; lean_object* v_bs_x27_2741_; lean_object* v___x_2742_; size_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v_v_2739_ = lean_array_uget(v_bs_2737_, v_i_2736_);
v___x_2740_ = lean_unsigned_to_nat(0u);
v_bs_x27_2741_ = lean_array_uset(v_bs_2737_, v_i_2736_, v___x_2740_);
v___x_2742_ = l_Lean_Fmt_TaggedDoc_nested(v_v_2739_);
v___x_2743_ = ((size_t)1ULL);
v___x_2744_ = lean_usize_add(v_i_2736_, v___x_2743_);
v___x_2745_ = lean_array_uset(v_bs_x27_2741_, v_i_2736_, v___x_2742_);
v_i_2736_ = v___x_2744_;
v_bs_2737_ = v___x_2745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object* v_sz_2747_, lean_object* v_i_2748_, lean_object* v_bs_2749_){
_start:
{
size_t v_sz_boxed_2750_; size_t v_i_boxed_2751_; lean_object* v_res_2752_; 
v_sz_boxed_2750_ = lean_unbox_usize(v_sz_2747_);
lean_dec(v_sz_2747_);
v_i_boxed_2751_ = lean_unbox_usize(v_i_2748_);
lean_dec(v_i_2748_);
v_res_2752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_boxed_2750_, v_i_boxed_2751_, v_bs_2749_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object* v_subAlts_2753_, lean_object* v_arrowTk_2754_, lean_object* v_rhs_2755_){
_start:
{
lean_object* v___y_2757_; uint8_t v___y_2758_; lean_object* v___y_2759_; uint8_t v___y_2799_; uint8_t v___x_2816_; 
v___x_2816_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_arrowTk_2754_);
if (v___x_2816_ == 0)
{
v___y_2799_ = v___x_2816_;
goto v___jp_2798_;
}
else
{
uint8_t v___x_2817_; 
v___x_2817_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_2755_);
v___y_2799_ = v___x_2817_;
goto v___jp_2798_;
}
v___jp_2756_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v_lhs_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v_nonStickyDoc_2775_; lean_object* v_flat_2776_; lean_object* v___x_2777_; 
v___x_2760_ = l_Lean_Fmt_Layouts_lines(v___y_2759_);
lean_dec_ref(v___y_2759_);
v___x_2761_ = lean_unsigned_to_nat(2u);
v___x_2762_ = lean_mk_empty_array_with_capacity(v___x_2761_);
lean_inc_ref_n(v___x_2762_, 2);
v___x_2763_ = lean_array_push(v___x_2762_, v___x_2760_);
v___x_2764_ = lean_array_push(v___x_2763_, v_arrowTk_2754_);
v_lhs_2765_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2764_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_lhs_2765_);
v___x_2767_ = l_Lean_Fmt_TaggedDoc_nl;
lean_inc_ref(v___y_2757_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v___y_2757_);
lean_inc_ref(v___x_2766_);
v___x_2769_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2766_, v___x_2768_);
v___x_2770_ = lean_box(0);
lean_inc_ref(v_rhs_2755_);
v___x_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_rhs_2755_);
v___x_2772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2770_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
lean_ctor_set(v___x_2772_, 2, v___x_2770_);
v___x_2773_ = lean_array_push(v___x_2762_, v___x_2769_);
v___x_2774_ = lean_array_push(v___x_2773_, v___x_2772_);
v_nonStickyDoc_2775_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2774_);
lean_dec_ref(v___x_2774_);
lean_inc_ref(v_nonStickyDoc_2775_);
v_flat_2776_ = l_Lean_Fmt_TaggedDoc_flattened(v_nonStickyDoc_2775_);
v___x_2777_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_2755_);
if (lean_obj_tag(v___x_2777_) == 1)
{
lean_object* v_val_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2796_; 
v_val_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2796_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_val_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2796_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v_stickyVariant_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_stickyVariant_2782_ = lean_ctor_get(v_val_2778_, 0);
v___x_2783_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v___y_2757_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set(v___x_2784_, 1, v___y_2757_);
v___x_2785_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2766_, v___x_2784_);
lean_inc_ref(v_stickyVariant_2782_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v_stickyVariant_2782_);
v___x_2787_ = v___x_2780_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_stickyVariant_2782_);
v___x_2787_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v_stickyDoc_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2770_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
lean_ctor_set(v___x_2788_, 2, v___x_2770_);
v___x_2789_ = lean_array_push(v___x_2762_, v___x_2785_);
v___x_2790_ = lean_array_push(v___x_2789_, v___x_2788_);
v_stickyDoc_2791_ = l_Lean_Fmt_TaggedDoc_combine(v___x_2790_);
lean_dec_ref(v___x_2790_);
v___x_2792_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_2778_, v___y_2758_);
lean_dec(v_val_2778_);
v___x_2793_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_2775_, v_stickyDoc_2791_, v___x_2792_);
lean_dec(v___x_2792_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_flat_2776_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
return v___x_2794_;
}
}
}
else
{
lean_object* v___x_2797_; 
lean_dec(v___x_2777_);
lean_dec_ref_known(v___x_2766_, 1);
lean_dec_ref(v___x_2762_);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_flat_2776_);
lean_ctor_set(v___x_2797_, 1, v_nonStickyDoc_2775_);
return v___x_2797_;
}
}
v___jp_2798_:
{
if (v___y_2799_ == 0)
{
lean_object* v___x_2800_; size_t v_sz_2801_; size_t v___x_2802_; lean_object* v_subAlts_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2800_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_sz_2801_ = lean_array_size(v_subAlts_2753_);
v___x_2802_ = ((size_t)0ULL);
v_subAlts_2803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_2801_, v___x_2802_, v_subAlts_2753_);
v___x_2804_ = lean_array_get_size(v_subAlts_2803_);
v___x_2805_ = lean_unsigned_to_nat(1u);
v___x_2806_ = lean_nat_sub(v___x_2804_, v___x_2805_);
v___x_2807_ = lean_nat_dec_lt(v___x_2806_, v___x_2804_);
if (v___x_2807_ == 0)
{
lean_dec(v___x_2806_);
v___y_2757_ = v___x_2800_;
v___y_2758_ = v___y_2799_;
v___y_2759_ = v_subAlts_2803_;
goto v___jp_2756_;
}
else
{
lean_object* v_v_2808_; lean_object* v___x_2809_; lean_object* v_xs_x27_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_v_2808_ = lean_array_fget(v_subAlts_2803_, v___x_2806_);
v___x_2809_ = lean_box(0);
v_xs_x27_2810_ = lean_array_fset(v_subAlts_2803_, v___x_2806_, v___x_2809_);
v___x_2811_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2808_);
v___x_2812_ = lean_array_fset(v_xs_x27_2810_, v___x_2806_, v___x_2811_);
lean_dec(v___x_2806_);
v___y_2757_ = v___x_2800_;
v___y_2758_ = v___y_2799_;
v___y_2759_ = v___x_2812_;
goto v___jp_2756_;
}
}
else
{
lean_object* v_subAlts_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v_rhs_2755_);
lean_dec_ref(v_arrowTk_2754_);
v_subAlts_2813_ = l_Lean_Fmt_Layouts_lines(v_subAlts_2753_);
lean_dec_ref(v_subAlts_2753_);
lean_inc_ref(v_subAlts_2813_);
v___x_2814_ = l_Lean_Fmt_TaggedDoc_flattened(v_subAlts_2813_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_subAlts_2813_);
return v___x_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(size_t v_sz_2818_, size_t v_i_2819_, lean_object* v_bs_2820_){
_start:
{
uint8_t v___x_2821_; 
v___x_2821_ = lean_usize_dec_lt(v_i_2819_, v_sz_2818_);
if (v___x_2821_ == 0)
{
return v_bs_2820_;
}
else
{
lean_object* v_v_2822_; lean_object* v_flat_2823_; lean_object* v___x_2824_; lean_object* v_bs_x27_2825_; size_t v___x_2826_; size_t v___x_2827_; lean_object* v___x_2828_; 
v_v_2822_ = lean_array_uget_borrowed(v_bs_2820_, v_i_2819_);
v_flat_2823_ = lean_ctor_get(v_v_2822_, 0);
lean_inc_ref(v_flat_2823_);
v___x_2824_ = lean_unsigned_to_nat(0u);
v_bs_x27_2825_ = lean_array_uset(v_bs_2820_, v_i_2819_, v___x_2824_);
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2819_, v___x_2826_);
v___x_2828_ = lean_array_uset(v_bs_x27_2825_, v_i_2819_, v_flat_2823_);
v_i_2819_ = v___x_2827_;
v_bs_2820_ = v___x_2828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object* v_sz_2830_, lean_object* v_i_2831_, lean_object* v_bs_2832_){
_start:
{
size_t v_sz_boxed_2833_; size_t v_i_boxed_2834_; lean_object* v_res_2835_; 
v_sz_boxed_2833_ = lean_unbox_usize(v_sz_2830_);
lean_dec(v_sz_2830_);
v_i_boxed_2834_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_boxed_2833_, v_i_boxed_2834_, v_bs_2832_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t v_sz_2836_, size_t v_i_2837_, lean_object* v_bs_2838_){
_start:
{
uint8_t v___x_2839_; 
v___x_2839_ = lean_usize_dec_lt(v_i_2837_, v_sz_2836_);
if (v___x_2839_ == 0)
{
return v_bs_2838_;
}
else
{
lean_object* v_v_2840_; lean_object* v_nonFlat_2841_; lean_object* v___x_2842_; lean_object* v_bs_x27_2843_; size_t v___x_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v_v_2840_ = lean_array_uget_borrowed(v_bs_2838_, v_i_2837_);
v_nonFlat_2841_ = lean_ctor_get(v_v_2840_, 1);
lean_inc_ref(v_nonFlat_2841_);
v___x_2842_ = lean_unsigned_to_nat(0u);
v_bs_x27_2843_ = lean_array_uset(v_bs_2838_, v_i_2837_, v___x_2842_);
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = lean_usize_add(v_i_2837_, v___x_2844_);
v___x_2846_ = lean_array_uset(v_bs_x27_2843_, v_i_2837_, v_nonFlat_2841_);
v_i_2837_ = v___x_2845_;
v_bs_2838_ = v___x_2846_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object* v_sz_2848_, lean_object* v_i_2849_, lean_object* v_bs_2850_){
_start:
{
size_t v_sz_boxed_2851_; size_t v_i_boxed_2852_; lean_object* v_res_2853_; 
v_sz_boxed_2851_ = lean_unbox_usize(v_sz_2848_);
lean_dec(v_sz_2848_);
v_i_boxed_2852_ = lean_unbox_usize(v_i_2849_);
lean_dec(v_i_2849_);
v_res_2853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_boxed_2851_, v_i_boxed_2852_, v_bs_2850_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object* v_alts_2854_, uint8_t v_allowFlattenedAlts_2855_){
_start:
{
size_t v_sz_2856_; size_t v___x_2857_; lean_object* v___x_2858_; lean_object* v_unflattened_2859_; 
v_sz_2856_ = lean_array_size(v_alts_2854_);
v___x_2857_ = ((size_t)0ULL);
lean_inc_ref(v_alts_2854_);
v___x_2858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_2856_, v___x_2857_, v_alts_2854_);
v_unflattened_2859_ = l_Lean_Fmt_Layouts_lines(v___x_2858_);
lean_dec_ref(v___x_2858_);
if (v_allowFlattenedAlts_2855_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v_alts_2854_);
v___x_2860_ = l_Lean_Fmt_TaggedDoc_withPosition(v_unflattened_2859_);
return v___x_2860_;
}
else
{
lean_object* v___x_2861_; lean_object* v_flattened_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_2856_, v___x_2857_, v_alts_2854_);
v_flattened_2862_ = l_Lean_Fmt_Layouts_lines(v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = lean_unsigned_to_nat(2u);
v___x_2864_ = lean_mk_empty_array_with_capacity(v___x_2863_);
v___x_2865_ = lean_array_push(v___x_2864_, v_flattened_2862_);
v___x_2866_ = lean_array_push(v___x_2865_, v_unflattened_2859_);
v___x_2867_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2866_);
v___x_2868_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_2867_);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object* v_alts_2869_, lean_object* v_allowFlattenedAlts_2870_){
_start:
{
uint8_t v_allowFlattenedAlts_boxed_2871_; lean_object* v_res_2872_; 
v_allowFlattenedAlts_boxed_2871_ = lean_unbox(v_allowFlattenedAlts_2870_);
v_res_2872_ = l_Lean_Fmt_Layouts_alts(v_alts_2869_, v_allowFlattenedAlts_boxed_2871_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(uint8_t v_x_2873_){
_start:
{
if (v_x_2873_ == 0)
{
lean_object* v___x_2874_; 
v___x_2874_ = lean_unsigned_to_nat(0u);
return v___x_2874_;
}
else
{
lean_object* v___x_2875_; 
v___x_2875_ = lean_unsigned_to_nat(1u);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___boxed(lean_object* v_x_2876_){
_start:
{
uint8_t v_x_boxed_2877_; lean_object* v_res_2878_; 
v_x_boxed_2877_ = lean_unbox(v_x_2876_);
v_res_2878_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(v_x_boxed_2877_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object* v_k_2879_){
_start:
{
lean_inc(v_k_2879_);
return v_k_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object* v_k_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(v_k_2880_);
lean_dec(v_k_2880_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object* v_motive_2882_, lean_object* v_ctorIdx_2883_, uint8_t v_t_2884_, lean_object* v_h_2885_, lean_object* v_k_2886_){
_start:
{
lean_inc(v_k_2886_);
return v_k_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object* v_motive_2887_, lean_object* v_ctorIdx_2888_, lean_object* v_t_2889_, lean_object* v_h_2890_, lean_object* v_k_2891_){
_start:
{
uint8_t v_t_boxed_2892_; lean_object* v_res_2893_; 
v_t_boxed_2892_ = lean_unbox(v_t_2889_);
v_res_2893_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(v_motive_2887_, v_ctorIdx_2888_, v_t_boxed_2892_, v_h_2890_, v_k_2891_);
lean_dec(v_k_2891_);
lean_dec(v_ctorIdx_2888_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object* v_sticky_2894_){
_start:
{
lean_inc(v_sticky_2894_);
return v_sticky_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(v_sticky_2895_);
lean_dec(v_sticky_2895_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object* v_motive_2897_, uint8_t v_t_2898_, lean_object* v_h_2899_, lean_object* v_sticky_2900_){
_start:
{
lean_inc(v_sticky_2900_);
return v_sticky_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object* v_motive_2901_, lean_object* v_t_2902_, lean_object* v_h_2903_, lean_object* v_sticky_2904_){
_start:
{
uint8_t v_t_boxed_2905_; lean_object* v_res_2906_; 
v_t_boxed_2905_ = lean_unbox(v_t_2902_);
v_res_2906_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(v_motive_2901_, v_t_boxed_2905_, v_h_2903_, v_sticky_2904_);
lean_dec(v_sticky_2904_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_2907_){
_start:
{
lean_inc(v_nonSticky_2907_);
return v_nonSticky_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(v_nonSticky_2908_);
lean_dec(v_nonSticky_2908_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object* v_motive_2910_, uint8_t v_t_2911_, lean_object* v_h_2912_, lean_object* v_nonSticky_2913_){
_start:
{
lean_inc(v_nonSticky_2913_);
return v_nonSticky_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object* v_motive_2914_, lean_object* v_t_2915_, lean_object* v_h_2916_, lean_object* v_nonSticky_2917_){
_start:
{
uint8_t v_t_boxed_2918_; lean_object* v_res_2919_; 
v_t_boxed_2918_ = lean_unbox(v_t_2915_);
v_res_2919_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(v_motive_2914_, v_t_boxed_2918_, v_h_2916_, v_nonSticky_2917_);
lean_dec(v_nonSticky_2917_);
return v_res_2919_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2920_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_2921_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
lean_ctor_set(v___x_2922_, 1, v___x_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object* v_keywordTk_2923_, lean_object* v_seq_2924_, uint8_t v_format_2925_){
_start:
{
lean_object* v___x_2926_; uint8_t v___x_2927_; lean_object* v_doc_2928_; 
v___x_2926_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_2927_ = 1;
v_doc_2928_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_keywordTk_2923_, v___x_2926_, v_seq_2924_, v___x_2927_);
if (v_format_2925_ == 0)
{
lean_object* v___x_2929_; uint8_t v___x_2930_; lean_object* v___x_2931_; 
lean_inc_ref(v_doc_2928_);
v___x_2929_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_2928_);
v___x_2930_ = 1;
v___x_2931_ = l_Lean_Fmt_TaggedDoc_sticky(v___x_2929_, v_doc_2928_, v___x_2930_);
return v___x_2931_;
}
else
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_2928_);
return v___x_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object* v_keywordTk_2933_, lean_object* v_seq_2934_, lean_object* v_format_2935_){
_start:
{
uint8_t v_format_boxed_2936_; lean_object* v_res_2937_; 
v_format_boxed_2936_ = lean_unbox(v_format_2935_);
v_res_2937_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_keywordTk_2933_, v_seq_2934_, v_format_boxed_2936_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(uint8_t v_x_2938_){
_start:
{
if (v_x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_unsigned_to_nat(0u);
return v___x_2939_;
}
else
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_unsigned_to_nat(1u);
return v___x_2940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___boxed(lean_object* v_x_2941_){
_start:
{
uint8_t v_x_boxed_2942_; lean_object* v_res_2943_; 
v_x_boxed_2942_ = lean_unbox(v_x_2941_);
v_res_2943_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(v_x_boxed_2942_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object* v_k_2944_){
_start:
{
lean_inc(v_k_2944_);
return v_k_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object* v_k_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(v_k_2945_);
lean_dec(v_k_2945_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object* v_motive_2947_, lean_object* v_ctorIdx_2948_, uint8_t v_t_2949_, lean_object* v_h_2950_, lean_object* v_k_2951_){
_start:
{
lean_inc(v_k_2951_);
return v_k_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object* v_motive_2952_, lean_object* v_ctorIdx_2953_, lean_object* v_t_2954_, lean_object* v_h_2955_, lean_object* v_k_2956_){
_start:
{
uint8_t v_t_boxed_2957_; lean_object* v_res_2958_; 
v_t_boxed_2957_ = lean_unbox(v_t_2954_);
v_res_2958_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(v_motive_2952_, v_ctorIdx_2953_, v_t_boxed_2957_, v_h_2955_, v_k_2956_);
lean_dec(v_k_2956_);
lean_dec(v_ctorIdx_2953_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object* v_sticky_2959_){
_start:
{
lean_inc(v_sticky_2959_);
return v_sticky_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(v_sticky_2960_);
lean_dec(v_sticky_2960_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object* v_motive_2962_, uint8_t v_t_2963_, lean_object* v_h_2964_, lean_object* v_sticky_2965_){
_start:
{
lean_inc(v_sticky_2965_);
return v_sticky_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object* v_motive_2966_, lean_object* v_t_2967_, lean_object* v_h_2968_, lean_object* v_sticky_2969_){
_start:
{
uint8_t v_t_boxed_2970_; lean_object* v_res_2971_; 
v_t_boxed_2970_ = lean_unbox(v_t_2967_);
v_res_2971_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(v_motive_2966_, v_t_boxed_2970_, v_h_2968_, v_sticky_2969_);
lean_dec(v_sticky_2969_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_2972_){
_start:
{
lean_inc(v_nonSticky_2972_);
return v_nonSticky_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(v_nonSticky_2973_);
lean_dec(v_nonSticky_2973_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object* v_motive_2975_, uint8_t v_t_2976_, lean_object* v_h_2977_, lean_object* v_nonSticky_2978_){
_start:
{
lean_inc(v_nonSticky_2978_);
return v_nonSticky_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object* v_motive_2979_, lean_object* v_t_2980_, lean_object* v_h_2981_, lean_object* v_nonSticky_2982_){
_start:
{
uint8_t v_t_boxed_2983_; lean_object* v_res_2984_; 
v_t_boxed_2983_ = lean_unbox(v_t_2980_);
v_res_2984_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(v_motive_2979_, v_t_boxed_2983_, v_h_2981_, v_nonSticky_2982_);
lean_dec(v_nonSticky_2982_);
return v_res_2984_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2985_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_2986_ = l_Lean_Fmt_TaggedDoc_space;
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
lean_ctor_set(v___x_2987_, 1, v___x_2985_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object* v_keyword_2988_, lean_object* v_term_2989_, uint8_t v_format_2990_){
_start:
{
lean_object* v___y_2992_; uint8_t v___x_3007_; 
v___x_3007_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_term_2989_);
if (v___x_3007_ == 0)
{
uint8_t v___x_3008_; lean_object* v___y_3010_; uint8_t v___x_3023_; 
v___x_3008_ = 1;
lean_inc_ref(v_term_2989_);
v___x_3023_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_term_2989_, v___x_3007_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_inc_ref(v_keyword_2988_);
v___x_3024_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_2988_);
v___x_3025_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_term_2989_);
v___x_3026_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3024_, v___x_3025_, v_term_2989_, v___x_3008_);
v___x_3027_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3026_);
v___y_3010_ = v___x_3027_;
goto v___jp_3009_;
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_inc_ref(v_keyword_2988_);
v___x_3028_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_2988_);
v___x_3029_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v_term_2989_);
v___x_3030_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3028_, v___x_3029_, v_term_2989_, v___x_3008_);
v___y_3010_ = v___x_3030_;
goto v___jp_3009_;
}
v___jp_3009_:
{
if (v_format_2990_ == 0)
{
lean_object* v___x_3011_; 
lean_inc_ref(v_term_2989_);
v___x_3011_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_term_2989_);
if (lean_obj_tag(v___x_3011_) == 1)
{
lean_object* v_val_3012_; uint8_t v_kind_3013_; 
v_val_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_val_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v_kind_3013_ = lean_ctor_get_uint8(v_val_3012_, sizeof(void*)*1);
lean_dec(v_val_3012_);
if (v_kind_3013_ == 1)
{
v___y_2992_ = v___y_3010_;
goto v___jp_2991_;
}
else
{
if (v___x_3007_ == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3014_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_2988_);
v___x_3015_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3016_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3014_, v___x_3015_, v_term_2989_, v___x_3008_);
v___x_3017_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3010_, v___x_3016_, v_kind_3013_);
return v___x_3017_;
}
else
{
v___y_2992_ = v___y_3010_;
goto v___jp_2991_;
}
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; 
lean_dec(v___x_3011_);
v___x_3018_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_2988_);
v___x_3019_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3020_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3018_, v___x_3019_, v_term_2989_, v___x_3008_);
v___x_3021_ = 0;
v___x_3022_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3010_, v___x_3020_, v___x_3021_);
return v___x_3022_;
}
}
else
{
lean_dec_ref(v_term_2989_);
lean_dec_ref(v_keyword_2988_);
return v___y_3010_;
}
}
}
else
{
uint8_t v___x_3031_; 
lean_dec_ref(v_term_2989_);
v___x_3031_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keyword_2988_);
if (v___x_3031_ == 0)
{
if (v_format_2990_ == 0)
{
lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; 
lean_inc_ref(v_keyword_2988_);
v___x_3032_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_2988_);
v___x_3033_ = 0;
v___x_3034_ = l_Lean_Fmt_TaggedDoc_sticky(v_keyword_2988_, v___x_3032_, v___x_3033_);
return v___x_3034_;
}
else
{
return v_keyword_2988_;
}
}
else
{
lean_object* v___x_3035_; 
lean_dec_ref(v_keyword_2988_);
v___x_3035_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3035_;
}
}
v___jp_2991_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; lean_object* v___x_3006_; 
v___x_2993_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_2988_);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
v___x_2995_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_2996_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_2994_, v___x_2995_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_term_2989_);
v___x_2999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
lean_ctor_set(v___x_2999_, 2, v___x_2997_);
v___x_3000_ = lean_unsigned_to_nat(2u);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_3000_);
v___x_3002_ = lean_array_push(v___x_3001_, v___x_2996_);
v___x_3003_ = lean_array_push(v___x_3002_, v___x_2999_);
v___x_3004_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3003_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = 1;
v___x_3006_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_2992_, v___x_3004_, v___x_3005_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object* v_keyword_3036_, lean_object* v_term_3037_, lean_object* v_format_3038_){
_start:
{
uint8_t v_format_boxed_3039_; lean_object* v_res_3040_; 
v_format_boxed_3039_ = lean_unbox(v_format_3038_);
v_res_3040_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3036_, v_term_3037_, v_format_boxed_3039_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(uint8_t v_x_3041_){
_start:
{
if (v_x_3041_ == 0)
{
lean_object* v___x_3042_; 
v___x_3042_ = lean_unsigned_to_nat(0u);
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_unsigned_to_nat(1u);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___boxed(lean_object* v_x_3044_){
_start:
{
uint8_t v_x_boxed_3045_; lean_object* v_res_3046_; 
v_x_boxed_3045_ = lean_unbox(v_x_3044_);
v_res_3046_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(v_x_boxed_3045_);
return v_res_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object* v_k_3047_){
_start:
{
lean_inc(v_k_3047_);
return v_k_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object* v_k_3048_){
_start:
{
lean_object* v_res_3049_; 
v_res_3049_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(v_k_3048_);
lean_dec(v_k_3048_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object* v_motive_3050_, lean_object* v_ctorIdx_3051_, uint8_t v_t_3052_, lean_object* v_h_3053_, lean_object* v_k_3054_){
_start:
{
lean_inc(v_k_3054_);
return v_k_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object* v_motive_3055_, lean_object* v_ctorIdx_3056_, lean_object* v_t_3057_, lean_object* v_h_3058_, lean_object* v_k_3059_){
_start:
{
uint8_t v_t_boxed_3060_; lean_object* v_res_3061_; 
v_t_boxed_3060_ = lean_unbox(v_t_3057_);
v_res_3061_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(v_motive_3055_, v_ctorIdx_3056_, v_t_boxed_3060_, v_h_3058_, v_k_3059_);
lean_dec(v_k_3059_);
lean_dec(v_ctorIdx_3056_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object* v_sticky_3062_){
_start:
{
lean_inc(v_sticky_3062_);
return v_sticky_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(v_sticky_3063_);
lean_dec(v_sticky_3063_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object* v_motive_3065_, uint8_t v_t_3066_, lean_object* v_h_3067_, lean_object* v_sticky_3068_){
_start:
{
lean_inc(v_sticky_3068_);
return v_sticky_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object* v_motive_3069_, lean_object* v_t_3070_, lean_object* v_h_3071_, lean_object* v_sticky_3072_){
_start:
{
uint8_t v_t_boxed_3073_; lean_object* v_res_3074_; 
v_t_boxed_3073_ = lean_unbox(v_t_3070_);
v_res_3074_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(v_motive_3069_, v_t_boxed_3073_, v_h_3071_, v_sticky_3072_);
lean_dec(v_sticky_3072_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3075_){
_start:
{
lean_inc(v_nonSticky_3075_);
return v_nonSticky_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(v_nonSticky_3076_);
lean_dec(v_nonSticky_3076_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object* v_motive_3078_, uint8_t v_t_3079_, lean_object* v_h_3080_, lean_object* v_nonSticky_3081_){
_start:
{
lean_inc(v_nonSticky_3081_);
return v_nonSticky_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object* v_motive_3082_, lean_object* v_t_3083_, lean_object* v_h_3084_, lean_object* v_nonSticky_3085_){
_start:
{
uint8_t v_t_boxed_3086_; lean_object* v_res_3087_; 
v_t_boxed_3086_ = lean_unbox(v_t_3083_);
v_res_3087_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(v_motive_3082_, v_t_boxed_3086_, v_h_3084_, v_nonSticky_3085_);
lean_dec(v_nonSticky_3085_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object* v_keyword_3088_, lean_object* v_alts_3089_, uint8_t v_format_3090_){
_start:
{
uint8_t v___x_3091_; lean_object* v_alts_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v_nonStickyDoc_3097_; 
v___x_3091_ = 1;
v_alts_3092_ = l_Lean_Fmt_Layouts_alts(v_alts_3089_, v___x_3091_);
v___x_3093_ = lean_unsigned_to_nat(2u);
v___x_3094_ = lean_mk_empty_array_with_capacity(v___x_3093_);
lean_inc_ref(v_keyword_3088_);
lean_inc_ref(v___x_3094_);
v___x_3095_ = lean_array_push(v___x_3094_, v_keyword_3088_);
lean_inc_ref(v_alts_3092_);
v___x_3096_ = lean_array_push(v___x_3095_, v_alts_3092_);
v_nonStickyDoc_3097_ = l_Lean_Fmt_Layouts_lines(v___x_3096_);
lean_dec_ref(v___x_3096_);
if (v_format_3090_ == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v_stickyDoc_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; 
v___x_3098_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3088_);
v___x_3099_ = lean_array_push(v___x_3094_, v___x_3098_);
v___x_3100_ = lean_array_push(v___x_3099_, v_alts_3092_);
v_stickyDoc_3101_ = l_Lean_Fmt_Layouts_lines(v___x_3100_);
lean_dec_ref(v___x_3100_);
v___x_3102_ = 0;
v___x_3103_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3097_, v_stickyDoc_3101_, v___x_3102_);
return v___x_3103_;
}
else
{
lean_dec_ref(v___x_3094_);
lean_dec_ref(v_alts_3092_);
lean_dec_ref(v_keyword_3088_);
return v_nonStickyDoc_3097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object* v_keyword_3104_, lean_object* v_alts_3105_, lean_object* v_format_3106_){
_start:
{
uint8_t v_format_boxed_3107_; lean_object* v_res_3108_; 
v_format_boxed_3107_ = lean_unbox(v_format_3106_);
v_res_3108_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_keyword_3104_, v_alts_3105_, v_format_boxed_3107_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(lean_object* v_x_3109_){
_start:
{
if (lean_obj_tag(v_x_3109_) == 0)
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_unsigned_to_nat(0u);
return v___x_3110_;
}
else
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_unsigned_to_nat(1u);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___boxed(lean_object* v_x_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(v_x_3112_);
lean_dec_ref(v_x_3112_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object* v_t_3114_, lean_object* v_k_3115_){
_start:
{
lean_object* v_sepArrayFormat_3116_; lean_object* v___x_3117_; 
v_sepArrayFormat_3116_ = lean_ctor_get(v_t_3114_, 0);
lean_inc_ref(v_sepArrayFormat_3116_);
lean_dec_ref(v_t_3114_);
v___x_3117_ = lean_apply_1(v_k_3115_, v_sepArrayFormat_3116_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object* v_motive_3118_, lean_object* v_ctorIdx_3119_, lean_object* v_t_3120_, lean_object* v_h_3121_, lean_object* v_k_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3120_, v_k_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object* v_motive_3124_, lean_object* v_ctorIdx_3125_, lean_object* v_t_3126_, lean_object* v_h_3127_, lean_object* v_k_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(v_motive_3124_, v_ctorIdx_3125_, v_t_3126_, v_h_3127_, v_k_3128_);
lean_dec(v_ctorIdx_3125_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object* v_t_3130_, lean_object* v_sticky_3131_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3130_, v_sticky_3131_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object* v_motive_3133_, lean_object* v_t_3134_, lean_object* v_h_3135_, lean_object* v_sticky_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3134_, v_sticky_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object* v_t_3138_, lean_object* v_nonSticky_3139_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3138_, v_nonSticky_3139_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object* v_motive_3141_, lean_object* v_t_3142_, lean_object* v_h_3143_, lean_object* v_nonSticky_3144_){
_start:
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3142_, v_nonSticky_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object* v_x_3146_){
_start:
{
if (lean_obj_tag(v_x_3146_) == 0)
{
uint8_t v___x_3147_; 
v___x_3147_ = 1;
return v___x_3147_;
}
else
{
uint8_t v___x_3148_; 
v___x_3148_ = 0;
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object* v_x_3149_){
_start:
{
uint8_t v_res_3150_; lean_object* v_r_3151_; 
v_res_3150_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_x_3149_);
lean_dec_ref(v_x_3149_);
v_r_3151_ = lean_box(v_res_3150_);
return v_r_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object* v_x_3152_){
_start:
{
lean_object* v_sepArrayFormat_3153_; 
v_sepArrayFormat_3153_ = lean_ctor_get(v_x_3152_, 0);
lean_inc_ref(v_sepArrayFormat_3153_);
return v_sepArrayFormat_3153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object* v_x_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(v_x_3154_);
lean_dec_ref(v_x_3154_);
return v_res_3155_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0(void){
_start:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3157_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
lean_ctor_set(v___x_3158_, 1, v___x_3156_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object* v_sep_3159_, lean_object* v_keyword_3160_, lean_object* v_sepArray_3161_, lean_object* v_format_3162_){
_start:
{
lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3202_; uint8_t v___y_3203_; lean_object* v___y_3209_; uint8_t v___y_3210_; lean_object* v___y_3226_; lean_object* v_sepArrayFormat_3229_; 
v_sepArrayFormat_3229_ = lean_ctor_get(v_format_3162_, 0);
lean_inc_ref(v_sepArrayFormat_3229_);
v___y_3226_ = v_sepArrayFormat_3229_;
goto v___jp_3225_;
v___jp_3163_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v_nonStickyDoc_3190_; uint8_t v___x_3191_; 
lean_inc_ref(v_keyword_3160_);
v___x_3167_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3160_);
v___x_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
v___x_3169_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v___x_3168_);
v___x_3170_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3168_, v___x_3169_);
v___x_3171_ = lean_box(0);
lean_inc_ref(v___y_3164_);
lean_inc_ref(v_sep_3159_);
v___x_3172_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3159_, v___y_3166_, v___y_3164_);
lean_dec_ref(v___y_3166_);
v___x_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
v___x_3174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3171_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
lean_ctor_set(v___x_3174_, 2, v___x_3171_);
v___x_3175_ = lean_unsigned_to_nat(2u);
v___x_3176_ = lean_mk_empty_array_with_capacity(v___x_3175_);
lean_inc_ref_n(v___x_3176_, 3);
v___x_3177_ = lean_array_push(v___x_3176_, v___x_3170_);
v___x_3178_ = lean_array_push(v___x_3177_, v___x_3174_);
v___x_3179_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3178_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_3181_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3168_, v___x_3180_);
v___x_3182_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3159_, v___y_3165_, v___y_3164_);
lean_dec_ref(v___y_3165_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3171_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
lean_ctor_set(v___x_3184_, 2, v___x_3171_);
v___x_3185_ = lean_array_push(v___x_3176_, v___x_3181_);
lean_inc_ref(v___x_3184_);
v___x_3186_ = lean_array_push(v___x_3185_, v___x_3184_);
v___x_3187_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3186_);
lean_dec_ref(v___x_3186_);
v___x_3188_ = lean_array_push(v___x_3176_, v___x_3179_);
v___x_3189_ = lean_array_push(v___x_3188_, v___x_3187_);
v_nonStickyDoc_3190_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3189_);
v___x_3191_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3162_);
lean_dec_ref(v_format_3162_);
if (v___x_3191_ == 0)
{
lean_dec_ref_known(v___x_3184_, 3);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v_keyword_3160_);
return v_nonStickyDoc_3190_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v_stickyDoc_3198_; uint8_t v___x_3199_; lean_object* v___x_3200_; 
v___x_3192_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3160_);
v___x_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
v___x_3194_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3195_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3193_, v___x_3194_);
v___x_3196_ = lean_array_push(v___x_3176_, v___x_3195_);
v___x_3197_ = lean_array_push(v___x_3196_, v___x_3184_);
v_stickyDoc_3198_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3197_);
lean_dec_ref(v___x_3197_);
v___x_3199_ = 0;
v___x_3200_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3190_, v_stickyDoc_3198_, v___x_3199_);
return v___x_3200_;
}
}
v___jp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3204_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3205_ = lean_unsigned_to_nat(0u);
v___x_3206_ = lean_array_get(v___x_3204_, v___y_3202_, v___x_3205_);
lean_dec_ref(v___y_3202_);
v___x_3207_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3160_, v___x_3206_, v___y_3203_);
return v___x_3207_;
}
v___jp_3208_:
{
lean_object* v_sepArray_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
lean_inc_ref(v_sep_3159_);
v_sepArray_3211_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_3159_, v_sepArray_3161_, v___y_3210_);
v___x_3212_ = lean_array_get_size(v_sepArray_3211_);
v___x_3213_ = lean_unsigned_to_nat(1u);
v___x_3214_ = lean_nat_dec_eq(v___x_3212_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; uint8_t v___x_3216_; 
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = lean_nat_dec_lt(v___x_3215_, v___x_3212_);
if (v___x_3216_ == 0)
{
lean_inc_ref(v_sepArray_3211_);
v___y_3164_ = v___y_3209_;
v___y_3165_ = v_sepArray_3211_;
v___y_3166_ = v_sepArray_3211_;
goto v___jp_3163_;
}
else
{
lean_object* v_v_3217_; lean_object* v___x_3218_; lean_object* v_xs_x27_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v_v_3217_ = lean_array_fget(v_sepArray_3211_, v___x_3215_);
v___x_3218_ = lean_box(0);
lean_inc_ref(v_sepArray_3211_);
v_xs_x27_3219_ = lean_array_fset(v_sepArray_3211_, v___x_3215_, v___x_3218_);
v___x_3220_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_3217_);
v___x_3221_ = lean_array_fset(v_xs_x27_3219_, v___x_3215_, v___x_3220_);
v___y_3164_ = v___y_3209_;
v___y_3165_ = v_sepArray_3211_;
v___y_3166_ = v___x_3221_;
goto v___jp_3163_;
}
}
else
{
uint8_t v___x_3222_; 
lean_dec_ref(v___y_3209_);
lean_dec_ref(v_sep_3159_);
v___x_3222_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3162_);
lean_dec_ref(v_format_3162_);
if (v___x_3222_ == 0)
{
uint8_t v___x_3223_; 
v___x_3223_ = 1;
v___y_3202_ = v_sepArray_3211_;
v___y_3203_ = v___x_3223_;
goto v___jp_3201_;
}
else
{
uint8_t v___x_3224_; 
v___x_3224_ = 0;
v___y_3202_ = v_sepArray_3211_;
v___y_3203_ = v___x_3224_;
goto v___jp_3201_;
}
}
}
v___jp_3225_:
{
if (lean_obj_tag(v___y_3226_) == 1)
{
uint8_t v_trailingSep_3227_; 
v_trailingSep_3227_ = lean_ctor_get_uint8(v___y_3226_, sizeof(void*)*1 + 1);
v___y_3209_ = v___y_3226_;
v___y_3210_ = v_trailingSep_3227_;
goto v___jp_3208_;
}
else
{
uint8_t v_trailingSep_3228_; 
v_trailingSep_3228_ = lean_ctor_get_uint8(v___y_3226_, sizeof(void*)*2);
v___y_3209_ = v___y_3226_;
v___y_3210_ = v_trailingSep_3228_;
goto v___jp_3208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object* v_sep_3230_, lean_object* v_keyword_3231_, lean_object* v_sepArray_3232_, lean_object* v_format_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3230_, v_keyword_3231_, v_sepArray_3232_, v_format_3233_);
lean_dec_ref(v_sepArray_3232_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(uint8_t v_x_3235_){
_start:
{
if (v_x_3235_ == 0)
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_unsigned_to_nat(0u);
return v___x_3236_;
}
else
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_unsigned_to_nat(1u);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___boxed(lean_object* v_x_3238_){
_start:
{
uint8_t v_x_boxed_3239_; lean_object* v_res_3240_; 
v_x_boxed_3239_ = lean_unbox(v_x_3238_);
v_res_3240_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(v_x_boxed_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object* v_k_3241_){
_start:
{
lean_inc(v_k_3241_);
return v_k_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object* v_k_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(v_k_3242_);
lean_dec(v_k_3242_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object* v_motive_3244_, lean_object* v_ctorIdx_3245_, uint8_t v_t_3246_, lean_object* v_h_3247_, lean_object* v_k_3248_){
_start:
{
lean_inc(v_k_3248_);
return v_k_3248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object* v_motive_3249_, lean_object* v_ctorIdx_3250_, lean_object* v_t_3251_, lean_object* v_h_3252_, lean_object* v_k_3253_){
_start:
{
uint8_t v_t_boxed_3254_; lean_object* v_res_3255_; 
v_t_boxed_3254_ = lean_unbox(v_t_3251_);
v_res_3255_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(v_motive_3249_, v_ctorIdx_3250_, v_t_boxed_3254_, v_h_3252_, v_k_3253_);
lean_dec(v_k_3253_);
lean_dec(v_ctorIdx_3250_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object* v_sticky_3256_){
_start:
{
lean_inc(v_sticky_3256_);
return v_sticky_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(v_sticky_3257_);
lean_dec(v_sticky_3257_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object* v_motive_3259_, uint8_t v_t_3260_, lean_object* v_h_3261_, lean_object* v_sticky_3262_){
_start:
{
lean_inc(v_sticky_3262_);
return v_sticky_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object* v_motive_3263_, lean_object* v_t_3264_, lean_object* v_h_3265_, lean_object* v_sticky_3266_){
_start:
{
uint8_t v_t_boxed_3267_; lean_object* v_res_3268_; 
v_t_boxed_3267_ = lean_unbox(v_t_3264_);
v_res_3268_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(v_motive_3263_, v_t_boxed_3267_, v_h_3265_, v_sticky_3266_);
lean_dec(v_sticky_3266_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3269_){
_start:
{
lean_inc(v_nonSticky_3269_);
return v_nonSticky_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(v_nonSticky_3270_);
lean_dec(v_nonSticky_3270_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object* v_motive_3272_, uint8_t v_t_3273_, lean_object* v_h_3274_, lean_object* v_nonSticky_3275_){
_start:
{
lean_inc(v_nonSticky_3275_);
return v_nonSticky_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object* v_motive_3276_, lean_object* v_t_3277_, lean_object* v_h_3278_, lean_object* v_nonSticky_3279_){
_start:
{
uint8_t v_t_boxed_3280_; lean_object* v_res_3281_; 
v_t_boxed_3280_ = lean_unbox(v_t_3277_);
v_res_3281_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(v_motive_3276_, v_t_boxed_3280_, v_h_3278_, v_nonSticky_3279_);
lean_dec(v_nonSticky_3279_);
return v_res_3281_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0(void){
_start:
{
lean_object* v_sepArrayFormat_3282_; lean_object* v___x_3283_; 
v_sepArrayFormat_3282_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepFill___closed__0, &l_Lean_Fmt_Layouts_sepFill___closed__0_once, _init_l_Lean_Fmt_Layouts_sepFill___closed__0);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v_sepArrayFormat_3282_);
return v___x_3283_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1(void){
_start:
{
lean_object* v_sepArrayFormat_3284_; lean_object* v___x_3285_; 
v_sepArrayFormat_3284_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepFill___closed__0, &l_Lean_Fmt_Layouts_sepFill___closed__0_once, _init_l_Lean_Fmt_Layouts_sepFill___closed__0);
v___x_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3285_, 0, v_sepArrayFormat_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object* v_sep_3286_, lean_object* v_keyword_3287_, lean_object* v_sepArray_3288_, uint8_t v_format_3289_){
_start:
{
if (v_format_3289_ == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0);
v___x_3291_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3286_, v_keyword_3287_, v_sepArray_3288_, v___x_3290_);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1, &l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1);
v___x_3293_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3286_, v_keyword_3287_, v_sepArray_3288_, v___x_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object* v_sep_3294_, lean_object* v_keyword_3295_, lean_object* v_sepArray_3296_, lean_object* v_format_3297_){
_start:
{
uint8_t v_format_boxed_3298_; lean_object* v_res_3299_; 
v_format_boxed_3298_ = lean_unbox(v_format_3297_);
v_res_3299_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v_sep_3294_, v_keyword_3295_, v_sepArray_3296_, v_format_boxed_3298_);
lean_dec_ref(v_sepArray_3296_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object* v_format_3300_, lean_object* v_a_3301_){
_start:
{
uint8_t v_nestedRhs_3302_; 
v_nestedRhs_3302_ = lean_ctor_get_uint8(v_format_3300_, 1);
if (v_nestedRhs_3302_ == 0)
{
return v_a_3301_;
}
else
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_Fmt_TaggedDoc_nested(v_a_3301_);
return v___x_3303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object* v_format_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(v_format_3304_, v_a_3305_);
lean_dec_ref(v_format_3304_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object* v_format_3307_){
_start:
{
uint8_t v_allowFlattening_3308_; 
v_allowFlattening_3308_ = lean_ctor_get_uint8(v_format_3307_, 0);
if (v_allowFlattening_3308_ == 0)
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_Fmt_TaggedDoc_hardNl;
return v___x_3309_;
}
else
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Fmt_TaggedDoc_nl;
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object* v_format_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3311_);
lean_dec_ref(v_format_3311_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object* v_rhs_3313_, lean_object* v_format_3314_, lean_object* v_lhs_3315_){
_start:
{
uint8_t v_allowFlattening_3316_; 
v_allowFlattening_3316_ = lean_ctor_get_uint8(v_format_3314_, 0);
if (v_allowFlattening_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3317_, 0, v_lhs_3315_);
v___x_3318_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3314_);
v___x_3319_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3319_, 0, v_format_3314_);
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3317_, v___x_3320_);
v___x_3322_ = lean_box(0);
v___x_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3323_, 0, v_rhs_3313_);
v___x_3324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
lean_ctor_set(v___x_3324_, 2, v___x_3322_);
v___x_3325_ = lean_unsigned_to_nat(2u);
v___x_3326_ = lean_mk_empty_array_with_capacity(v___x_3325_);
v___x_3327_ = lean_array_push(v___x_3326_, v___x_3321_);
v___x_3328_ = lean_array_push(v___x_3327_, v___x_3324_);
v___x_3329_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3328_);
lean_dec_ref(v___x_3328_);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3330_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3314_);
v___x_3331_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3331_, 0, v_format_3314_);
v___x_3332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3330_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_3315_, v___x_3332_, v_rhs_3313_, v_allowFlattening_3316_);
return v___x_3333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0(lean_object* v___y_3334_){
_start:
{
lean_inc_ref(v___y_3334_);
return v___y_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed(lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_Lean_Fmt_Layouts_keywordSeparated___lam__0(v___y_3335_);
lean_dec_ref(v___y_3335_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object* v_lhs_3338_, lean_object* v_keywordTk_3339_, lean_object* v_rhs_3340_, lean_object* v_format_3341_){
_start:
{
uint8_t v___x_3342_; 
v___x_3342_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keywordTk_3339_);
if (v___x_3342_ == 0)
{
lean_object* v___f_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v_trailingKeywordLhs_3349_; lean_object* v___x_3350_; lean_object* v_leadingKeywordRhs_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___f_3343_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3344_ = lean_unsigned_to_nat(2u);
v___x_3345_ = lean_mk_empty_array_with_capacity(v___x_3344_);
lean_inc_ref(v_lhs_3338_);
lean_inc_ref_n(v___x_3345_, 2);
v___x_3346_ = lean_array_push(v___x_3345_, v_lhs_3338_);
lean_inc_ref(v_keywordTk_3339_);
v___x_3347_ = lean_array_push(v___x_3346_, v_keywordTk_3339_);
v___x_3348_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3347_);
lean_dec_ref(v___x_3347_);
v_trailingKeywordLhs_3349_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3348_);
lean_inc_ref_n(v_format_3341_, 2);
lean_inc_ref(v_rhs_3340_);
v___x_3350_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3340_, v_format_3341_, v_keywordTk_3339_);
v_leadingKeywordRhs_3351_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3350_);
v___x_3352_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3340_, v_format_3341_, v_trailingKeywordLhs_3349_);
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_lhs_3338_);
v___x_3354_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3341_);
lean_dec_ref(v_format_3341_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v___f_3343_);
v___x_3356_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3353_, v___x_3355_);
v___x_3357_ = lean_box(0);
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v_leadingKeywordRhs_3351_);
v___x_3359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
lean_ctor_set(v___x_3359_, 2, v___x_3357_);
v___x_3360_ = lean_array_push(v___x_3345_, v___x_3356_);
v___x_3361_ = lean_array_push(v___x_3360_, v___x_3359_);
v___x_3362_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3361_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = lean_array_push(v___x_3345_, v___x_3352_);
v___x_3364_ = lean_array_push(v___x_3363_, v___x_3362_);
v___x_3365_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3364_);
v___x_3366_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3365_);
return v___x_3366_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec_ref(v_keywordTk_3339_);
v___x_3367_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3340_, v_format_3341_, v_lhs_3338_);
v___x_3368_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3367_);
return v___x_3368_;
}
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0(void){
_start:
{
lean_object* v___f_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___f_3369_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3370_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
lean_ctor_set(v___x_3371_, 1, v___f_3369_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object* v_terms_3372_){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3373_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3374_ = lean_box(0);
v___x_3375_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_terms_3372_);
v___x_3376_ = lean_array_pop(v_terms_3372_);
v___x_3377_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_3375_, v___x_3376_);
v___x_3378_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3377_);
v___x_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3374_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
lean_ctor_set(v___x_3380_, 2, v___x_3374_);
v___x_3381_ = lean_array_get_size(v_terms_3372_);
v___x_3382_ = lean_unsigned_to_nat(1u);
v___x_3383_ = lean_nat_sub(v___x_3381_, v___x_3382_);
v___x_3384_ = lean_array_get(v___x_3373_, v_terms_3372_, v___x_3383_);
lean_dec(v___x_3383_);
lean_dec_ref(v_terms_3372_);
v___x_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
v___x_3386_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_3387_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_3385_, v___x_3386_);
v___x_3388_ = lean_unsigned_to_nat(2u);
v___x_3389_ = lean_mk_empty_array_with_capacity(v___x_3388_);
v___x_3390_ = lean_array_push(v___x_3389_, v___x_3380_);
v___x_3391_ = lean_array_push(v___x_3390_, v___x_3387_);
v___x_3392_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3391_);
lean_dec_ref(v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3394_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object* v_app_3395_, lean_object* v_fillableTerms_3396_, lean_object* v_terms_3397_, lean_object* v_eligibleKinds_3398_){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; uint8_t v_allowFill_3405_; 
v___x_3399_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3400_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3401_ = lean_array_get_size(v_fillableTerms_3396_);
v___x_3402_ = lean_unsigned_to_nat(1u);
v___x_3403_ = lean_nat_sub(v___x_3401_, v___x_3402_);
v___x_3404_ = lean_array_get_borrowed(v___x_3400_, v_fillableTerms_3396_, v___x_3403_);
lean_dec(v___x_3403_);
v_allowFill_3405_ = lean_ctor_get_uint8(v___x_3404_, sizeof(void*)*1);
if (v_allowFill_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_dec_ref(v_terms_3397_);
lean_dec_ref(v_app_3395_);
v___x_3406_ = lean_box(0);
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = lean_array_get_size(v_terms_3397_);
v___x_3408_ = lean_nat_sub(v___x_3407_, v___x_3402_);
v___x_3409_ = lean_array_get_borrowed(v___x_3399_, v_terms_3397_, v___x_3408_);
lean_inc(v___x_3409_);
v___x_3410_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v___x_3409_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v___x_3411_; 
lean_dec(v___x_3408_);
lean_dec_ref(v_terms_3397_);
lean_dec_ref(v_app_3395_);
v___x_3411_ = lean_box(0);
return v___x_3411_;
}
else
{
lean_object* v_val_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3433_; 
v_val_3412_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3414_ = v___x_3410_;
v_isShared_3415_ = v_isSharedCheck_3433_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_val_3412_);
lean_dec(v___x_3410_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3433_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
uint8_t v___x_3416_; uint8_t v___x_3417_; lean_object* v___y_3419_; 
v___x_3416_ = lean_unbox(v_val_3412_);
lean_dec(v_val_3412_);
v___x_3417_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_3398_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3428_; 
lean_del_object(v___x_3414_);
lean_dec(v___x_3408_);
lean_dec_ref(v_terms_3397_);
lean_dec_ref(v_app_3395_);
v___x_3428_ = lean_box(0);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; 
lean_inc(v___x_3409_);
v___x_3429_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_3409_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_3431_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_3430_);
v___y_3419_ = v___x_3431_;
goto v___jp_3418_;
}
else
{
lean_object* v_val_3432_; 
v_val_3432_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_val_3432_);
lean_dec_ref_known(v___x_3429_, 1);
v___y_3419_ = v_val_3432_;
goto v___jp_3418_;
}
}
v___jp_3418_:
{
lean_object* v_stickyVariant_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3426_; 
v_stickyVariant_3420_ = lean_ctor_get(v___y_3419_, 0);
lean_inc_ref(v_stickyVariant_3420_);
v___x_3421_ = lean_array_set(v_terms_3397_, v___x_3408_, v_stickyVariant_3420_);
lean_dec(v___x_3408_);
v___x_3422_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v___x_3421_);
v___x_3423_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_3419_, v___x_3417_);
lean_dec_ref(v___y_3419_);
v___x_3424_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_app_3395_, v___x_3422_, v___x_3423_);
lean_dec(v___x_3423_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v___x_3424_);
v___x_3426_ = v___x_3414_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3424_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object* v_app_3434_, lean_object* v_fillableTerms_3435_, lean_object* v_terms_3436_, lean_object* v_eligibleKinds_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3434_, v_fillableTerms_3435_, v_terms_3436_, v_eligibleKinds_3437_);
lean_dec_ref(v_eligibleKinds_3437_);
lean_dec_ref(v_fillableTerms_3435_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object* v_format_3439_, lean_object* v_app_3440_, lean_object* v_terms_3441_){
_start:
{
uint8_t v_sparse_3442_; 
v_sparse_3442_ = lean_ctor_get_uint8(v_format_3439_, 1);
if (v_sparse_3442_ == 0)
{
uint8_t v_respectPseudoAlignment_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_respectPseudoAlignment_3443_ = lean_ctor_get_uint8(v_format_3439_, 3);
v___x_3444_ = lean_array_get_size(v_terms_3441_);
v___x_3445_ = lean_unsigned_to_nat(2u);
v___x_3446_ = lean_nat_dec_eq(v___x_3444_, v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec_ref(v_terms_3441_);
lean_dec_ref(v_app_3440_);
v___x_3447_ = lean_box(0);
return v___x_3447_;
}
else
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; uint8_t v___x_3452_; 
v___x_3448_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3449_ = lean_unsigned_to_nat(1u);
v___x_3450_ = lean_nat_sub(v___x_3444_, v___x_3449_);
v___x_3451_ = lean_array_get_borrowed(v___x_3448_, v_terms_3441_, v___x_3450_);
lean_dec(v___x_3450_);
lean_inc(v___x_3451_);
v___x_3452_ = l_Lean_Fmt_Layouts_permitDenseLayout(v___x_3451_, v_respectPseudoAlignment_3443_);
if (v___x_3452_ == 0)
{
lean_object* v___x_3453_; 
lean_dec_ref(v_terms_3441_);
lean_dec_ref(v_app_3440_);
v___x_3453_ = lean_box(0);
return v___x_3453_;
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3454_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v_terms_3441_);
v___x_3455_ = lean_mk_empty_array_with_capacity(v___x_3445_);
v___x_3456_ = lean_array_push(v___x_3455_, v___x_3454_);
v___x_3457_ = lean_array_push(v___x_3456_, v_app_3440_);
v___x_3458_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3457_);
v___x_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
return v___x_3459_;
}
}
}
else
{
lean_object* v___x_3460_; 
lean_dec_ref(v_terms_3441_);
lean_dec_ref(v_app_3440_);
v___x_3460_ = lean_box(0);
return v___x_3460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object* v_format_3461_, lean_object* v_app_3462_, lean_object* v_terms_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3461_, v_app_3462_, v_terms_3463_);
lean_dec_ref(v_format_3461_);
return v_res_3464_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0));
v___x_3467_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3466_);
return v___x_3467_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3468_; lean_object* v_lbTk_3469_; 
v___x_3468_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1);
v_lbTk_3469_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3468_);
return v_lbTk_3469_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3));
v___x_3472_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3473_; lean_object* v_rbTk_3474_; 
v___x_3473_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4);
v_rbTk_3474_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3473_);
return v_rbTk_3474_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object* v_upperBound_3475_, lean_object* v_a_3476_, lean_object* v_b_3477_){
_start:
{
lean_object* v_a_3479_; uint8_t v___x_3483_; 
v___x_3483_ = lean_nat_dec_lt(v_a_3476_, v_upperBound_3475_);
if (v___x_3483_ == 0)
{
lean_dec(v_a_3476_);
return v_b_3477_;
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v_v_3486_; uint8_t v_allowFill_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3499_; 
v___x_3484_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3485_ = lean_array_get(v___x_3484_, v_b_3477_, v_a_3476_);
v_v_3486_ = lean_ctor_get(v___x_3485_, 0);
v_allowFill_3487_ = lean_ctor_get_uint8(v___x_3485_, sizeof(void*)*1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3489_ = v___x_3485_;
v_isShared_3490_ = v_isSharedCheck_3499_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_v_3486_);
lean_dec(v___x_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3499_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
uint8_t v___x_3491_; 
lean_inc(v_v_3486_);
v___x_3491_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_v_3486_);
if (v___x_3491_ == 0)
{
lean_del_object(v___x_3489_);
lean_dec(v_v_3486_);
v_a_3479_ = v_b_3477_;
goto v___jp_3478_;
}
else
{
lean_object* v_lbTk_3492_; lean_object* v_rbTk_3493_; lean_object* v___x_3494_; lean_object* v___x_3496_; 
v_lbTk_3492_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2);
v_rbTk_3493_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5);
v___x_3494_ = l_Lean_Fmt_Layouts_parens(v_lbTk_3492_, v_v_3486_, v_rbTk_3493_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3494_);
v___x_3496_ = v___x_3489_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3494_);
lean_ctor_set_uint8(v_reuseFailAlloc_3498_, sizeof(void*)*1, v_allowFill_3487_);
v___x_3496_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_array_set(v_b_3477_, v_a_3476_, v___x_3496_);
v_a_3479_ = v___x_3497_;
goto v___jp_3478_;
}
}
}
}
v___jp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = lean_unsigned_to_nat(1u);
v___x_3481_ = lean_nat_add(v_a_3476_, v___x_3480_);
lean_dec(v_a_3476_);
v_a_3476_ = v___x_3481_;
v_b_3477_ = v_a_3479_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object* v_upperBound_3500_, lean_object* v_a_3501_, lean_object* v_b_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3500_, v_a_3501_, v_b_3502_);
lean_dec(v_upperBound_3500_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object* v_as_3504_, size_t v_i_3505_, size_t v_stop_3506_, lean_object* v_b_3507_){
_start:
{
lean_object* v___y_3509_; uint8_t v___x_3513_; 
v___x_3513_ = lean_usize_dec_eq(v_i_3505_, v_stop_3506_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v_v_3515_; uint8_t v___x_3516_; 
v___x_3514_ = lean_array_uget_borrowed(v_as_3504_, v_i_3505_);
v_v_3515_ = lean_ctor_get(v___x_3514_, 0);
v___x_3516_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_3515_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
lean_inc(v___x_3514_);
v___x_3517_ = lean_array_push(v_b_3507_, v___x_3514_);
v___y_3509_ = v___x_3517_;
goto v___jp_3508_;
}
else
{
v___y_3509_ = v_b_3507_;
goto v___jp_3508_;
}
}
else
{
return v_b_3507_;
}
v___jp_3508_:
{
size_t v___x_3510_; size_t v___x_3511_; 
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_add(v_i_3505_, v___x_3510_);
v_i_3505_ = v___x_3511_;
v_b_3507_ = v___y_3509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object* v_as_3518_, lean_object* v_i_3519_, lean_object* v_stop_3520_, lean_object* v_b_3521_){
_start:
{
size_t v_i_boxed_3522_; size_t v_stop_boxed_3523_; lean_object* v_res_3524_; 
v_i_boxed_3522_ = lean_unbox_usize(v_i_3519_);
lean_dec(v_i_3519_);
v_stop_boxed_3523_ = lean_unbox_usize(v_stop_3520_);
lean_dec(v_stop_3520_);
v_res_3524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_as_3518_, v_i_boxed_3522_, v_stop_boxed_3523_, v_b_3521_);
lean_dec_ref(v_as_3518_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t v_sz_3525_, size_t v_i_3526_, lean_object* v_bs_3527_){
_start:
{
uint8_t v___x_3528_; 
v___x_3528_ = lean_usize_dec_lt(v_i_3526_, v_sz_3525_);
if (v___x_3528_ == 0)
{
return v_bs_3527_;
}
else
{
lean_object* v_v_3529_; lean_object* v_v_3530_; lean_object* v___x_3531_; lean_object* v_bs_x27_3532_; size_t v___x_3533_; size_t v___x_3534_; lean_object* v___x_3535_; 
v_v_3529_ = lean_array_uget_borrowed(v_bs_3527_, v_i_3526_);
v_v_3530_ = lean_ctor_get(v_v_3529_, 0);
lean_inc(v_v_3530_);
v___x_3531_ = lean_unsigned_to_nat(0u);
v_bs_x27_3532_ = lean_array_uset(v_bs_3527_, v_i_3526_, v___x_3531_);
v___x_3533_ = ((size_t)1ULL);
v___x_3534_ = lean_usize_add(v_i_3526_, v___x_3533_);
v___x_3535_ = lean_array_uset(v_bs_x27_3532_, v_i_3526_, v_v_3530_);
v_i_3526_ = v___x_3534_;
v_bs_3527_ = v___x_3535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object* v_sz_3537_, lean_object* v_i_3538_, lean_object* v_bs_3539_){
_start:
{
size_t v_sz_boxed_3540_; size_t v_i_boxed_3541_; lean_object* v_res_3542_; 
v_sz_boxed_3540_ = lean_unbox_usize(v_sz_3537_);
lean_dec(v_sz_3537_);
v_i_boxed_3541_ = lean_unbox_usize(v_i_3538_);
lean_dec(v_i_3538_);
v_res_3542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_boxed_3540_, v_i_boxed_3541_, v_bs_3539_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object* v_terms_3545_, lean_object* v_format_3546_){
_start:
{
lean_object* v_app_3548_; lean_object* v_fillableTerms_3552_; lean_object* v___y_3566_; lean_object* v_fillableTerms_3567_; lean_object* v___x_3572_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; uint8_t v___y_3577_; lean_object* v___y_3594_; lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3572_ = lean_unsigned_to_nat(0u);
v___x_3605_ = lean_array_get_size(v_terms_3545_);
v___x_3606_ = ((lean_object*)(l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0));
v___x_3607_ = lean_nat_dec_lt(v___x_3572_, v___x_3605_);
if (v___x_3607_ == 0)
{
v___y_3594_ = v___x_3606_;
goto v___jp_3593_;
}
else
{
uint8_t v___x_3608_; 
v___x_3608_ = lean_nat_dec_le(v___x_3605_, v___x_3605_);
if (v___x_3608_ == 0)
{
if (v___x_3607_ == 0)
{
v___y_3594_ = v___x_3606_;
goto v___jp_3593_;
}
else
{
size_t v___x_3609_; size_t v___x_3610_; lean_object* v___x_3611_; 
v___x_3609_ = ((size_t)0ULL);
v___x_3610_ = lean_usize_of_nat(v___x_3605_);
v___x_3611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3545_, v___x_3609_, v___x_3610_, v___x_3606_);
v___y_3594_ = v___x_3611_;
goto v___jp_3593_;
}
}
else
{
size_t v___x_3612_; size_t v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = ((size_t)0ULL);
v___x_3613_ = lean_usize_of_nat(v___x_3605_);
v___x_3614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3545_, v___x_3612_, v___x_3613_, v___x_3606_);
v___y_3594_ = v___x_3614_;
goto v___jp_3593_;
}
}
v___jp_3547_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = l_Lean_Fmt_TaggedDoc_nested(v_app_3548_);
v___x_3550_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3549_);
return v___x_3550_;
}
v___jp_3551_:
{
lean_object* v_app_3553_; size_t v_sz_3554_; size_t v___x_3555_; lean_object* v_terms_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_inc_ref_n(v_fillableTerms_3552_, 2);
v_app_3553_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(v_fillableTerms_3552_);
v_sz_3554_ = lean_array_size(v_fillableTerms_3552_);
v___x_3555_ = ((size_t)0ULL);
v_terms_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_3554_, v___x_3555_, v_fillableTerms_3552_);
v___x_3557_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
lean_inc_ref(v_terms_3556_);
lean_inc_ref(v_app_3553_);
v___x_3558_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3553_, v_fillableTerms_3552_, v_terms_3556_, v___x_3557_);
if (lean_obj_tag(v___x_3558_) == 1)
{
lean_object* v_val_3559_; 
lean_dec_ref(v_terms_3556_);
lean_dec_ref(v_app_3553_);
lean_dec_ref(v_fillableTerms_3552_);
v_val_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_val_3559_);
lean_dec_ref_known(v___x_3558_, 1);
v_app_3548_ = v_val_3559_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3560_; 
lean_dec(v___x_3558_);
lean_inc_ref(v_terms_3556_);
lean_inc_ref(v_app_3553_);
v___x_3560_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3546_, v_app_3553_, v_terms_3556_);
if (lean_obj_tag(v___x_3560_) == 1)
{
lean_object* v_val_3561_; 
lean_dec_ref(v_terms_3556_);
lean_dec_ref(v_app_3553_);
lean_dec_ref(v_fillableTerms_3552_);
v_val_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_val_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v_app_3548_ = v_val_3561_;
goto v___jp_3547_;
}
else
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
lean_dec(v___x_3560_);
v___x_3562_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
lean_inc_ref(v_app_3553_);
v___x_3563_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3553_, v_fillableTerms_3552_, v_terms_3556_, v___x_3562_);
lean_dec_ref(v_fillableTerms_3552_);
if (lean_obj_tag(v___x_3563_) == 1)
{
lean_object* v_val_3564_; 
lean_dec_ref(v_app_3553_);
v_val_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_val_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v_app_3548_ = v_val_3564_;
goto v___jp_3547_;
}
else
{
lean_dec(v___x_3563_);
v_app_3548_ = v_app_3553_;
goto v___jp_3547_;
}
}
}
}
v___jp_3565_:
{
uint8_t v_parenthesize_3568_; 
v_parenthesize_3568_ = lean_ctor_get_uint8(v_format_3546_, 2);
if (v_parenthesize_3568_ == 0)
{
lean_dec(v___y_3566_);
v_fillableTerms_3552_ = v_fillableTerms_3567_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = lean_array_get_size(v_fillableTerms_3567_);
v___x_3570_ = lean_nat_sub(v___x_3569_, v___y_3566_);
v___x_3571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v___x_3570_, v___y_3566_, v_fillableTerms_3567_);
lean_dec(v___x_3570_);
v_fillableTerms_3552_ = v___x_3571_;
goto v___jp_3551_;
}
}
v___jp_3573_:
{
if (v___y_3577_ == 0)
{
lean_dec(v___y_3575_);
v___y_3566_ = v___y_3574_;
v_fillableTerms_3567_ = v___y_3576_;
goto v___jp_3565_;
}
else
{
uint8_t v___x_3578_; 
v___x_3578_ = lean_nat_dec_lt(v___x_3572_, v___y_3575_);
lean_dec(v___y_3575_);
if (v___x_3578_ == 0)
{
v___y_3566_ = v___y_3574_;
v_fillableTerms_3567_ = v___y_3576_;
goto v___jp_3565_;
}
else
{
lean_object* v_v_3579_; lean_object* v_v_3580_; uint8_t v_allowFill_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3592_; 
v_v_3579_ = lean_array_fget(v___y_3576_, v___x_3572_);
v_v_3580_ = lean_ctor_get(v_v_3579_, 0);
v_allowFill_3581_ = lean_ctor_get_uint8(v_v_3579_, sizeof(void*)*1);
v_isSharedCheck_3592_ = !lean_is_exclusive(v_v_3579_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3583_ = v_v_3579_;
v_isShared_3584_ = v_isSharedCheck_3592_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_v_3580_);
lean_dec(v_v_3579_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3592_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v_xs_x27_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3585_ = lean_box(0);
v_xs_x27_3586_ = lean_array_fset(v___y_3576_, v___x_3572_, v___x_3585_);
v___x_3587_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3580_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3587_);
v___x_3589_ = v___x_3583_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3587_);
lean_ctor_set_uint8(v_reuseFailAlloc_3591_, sizeof(void*)*1, v_allowFill_3581_);
v___x_3589_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; 
v___x_3590_ = lean_array_fset(v_xs_x27_3586_, v___x_3572_, v___x_3589_);
v___y_3566_ = v___y_3574_;
v_fillableTerms_3567_ = v___x_3590_;
goto v___jp_3565_;
}
}
}
}
}
v___jp_3593_:
{
lean_object* v___x_3595_; uint8_t v___x_3596_; 
v___x_3595_ = lean_array_get_size(v___y_3594_);
v___x_3596_ = lean_nat_dec_eq(v___x_3595_, v___x_3572_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3597_ = lean_unsigned_to_nat(1u);
v___x_3598_ = lean_nat_dec_eq(v___x_3595_, v___x_3597_);
if (v___x_3598_ == 0)
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_nat_dec_lt(v___x_3597_, v___x_3595_);
if (v___x_3599_ == 0)
{
v___y_3574_ = v___x_3597_;
v___y_3575_ = v___x_3595_;
v___y_3576_ = v___y_3594_;
v___y_3577_ = v___x_3599_;
goto v___jp_3573_;
}
else
{
uint8_t v_hardNestedFirstTerm_3600_; 
v_hardNestedFirstTerm_3600_ = lean_ctor_get_uint8(v_format_3546_, 0);
v___y_3574_ = v___x_3597_;
v___y_3575_ = v___x_3595_;
v___y_3576_ = v___y_3594_;
v___y_3577_ = v_hardNestedFirstTerm_3600_;
goto v___jp_3573_;
}
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_v_3603_; 
v___x_3601_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3602_ = lean_array_get(v___x_3601_, v___y_3594_, v___x_3572_);
lean_dec_ref(v___y_3594_);
v_v_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_v_3603_);
lean_dec(v___x_3602_);
return v_v_3603_;
}
}
else
{
lean_object* v___x_3604_; 
lean_dec_ref(v___y_3594_);
v___x_3604_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object* v_terms_3615_, lean_object* v_format_3616_){
_start:
{
lean_object* v_res_3617_; 
v_res_3617_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v_terms_3615_, v_format_3616_);
lean_dec_ref(v_format_3616_);
lean_dec_ref(v_terms_3615_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object* v_upperBound_3618_, lean_object* v_inst_3619_, lean_object* v_R_3620_, lean_object* v_a_3621_, lean_object* v_b_3622_, lean_object* v_c_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3618_, v_a_3621_, v_b_3622_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object* v_upperBound_3625_, lean_object* v_inst_3626_, lean_object* v_R_3627_, lean_object* v_a_3628_, lean_object* v_b_3629_, lean_object* v_c_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(v_upperBound_3625_, v_inst_3626_, v_R_3627_, v_a_3628_, v_b_3629_, v_c_3630_);
lean_dec(v_upperBound_3625_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t v_sz_3632_, size_t v_i_3633_, lean_object* v_bs_3634_){
_start:
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_usize_dec_lt(v_i_3633_, v_sz_3632_);
if (v___x_3635_ == 0)
{
return v_bs_3634_;
}
else
{
lean_object* v_v_3636_; lean_object* v___x_3637_; lean_object* v_bs_x27_3638_; lean_object* v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; lean_object* v___x_3642_; 
v_v_3636_ = lean_array_uget(v_bs_3634_, v_i_3633_);
v___x_3637_ = lean_unsigned_to_nat(0u);
v_bs_x27_3638_ = lean_array_uset(v_bs_3634_, v_i_3633_, v___x_3637_);
v___x_3639_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3639_, 0, v_v_3636_);
lean_ctor_set_uint8(v___x_3639_, sizeof(void*)*1, v___x_3635_);
v___x_3640_ = ((size_t)1ULL);
v___x_3641_ = lean_usize_add(v_i_3633_, v___x_3640_);
v___x_3642_ = lean_array_uset(v_bs_x27_3638_, v_i_3633_, v___x_3639_);
v_i_3633_ = v___x_3641_;
v_bs_3634_ = v___x_3642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object* v_sz_3644_, lean_object* v_i_3645_, lean_object* v_bs_3646_){
_start:
{
size_t v_sz_boxed_3647_; size_t v_i_boxed_3648_; lean_object* v_res_3649_; 
v_sz_boxed_3647_ = lean_unbox_usize(v_sz_3644_);
lean_dec(v_sz_3644_);
v_i_boxed_3648_ = lean_unbox_usize(v_i_3645_);
lean_dec(v_i_3645_);
v_res_3649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_boxed_3647_, v_i_boxed_3648_, v_bs_3646_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object* v_terms_3650_, lean_object* v_format_3651_){
_start:
{
size_t v_sz_3652_; size_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v_sz_3652_ = lean_array_size(v_terms_3650_);
v___x_3653_ = ((size_t)0ULL);
v___x_3654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_3652_, v___x_3653_, v_terms_3650_);
v___x_3655_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_3654_, v_format_3651_);
lean_dec_ref(v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object* v_terms_3656_, lean_object* v_format_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Fmt_Layouts_application(v_terms_3656_, v_format_3657_);
lean_dec_ref(v_format_3657_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object* v_f_3659_){
_start:
{
uint8_t v_hardNestedFirstTerm_3660_; uint8_t v_sparse_3661_; uint8_t v_parenthesize_3662_; uint8_t v_respectPseudoAlignment_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v_hardNestedFirstTerm_3660_ = lean_ctor_get_uint8(v_f_3659_, 0);
v_sparse_3661_ = lean_ctor_get_uint8(v_f_3659_, 1);
v_parenthesize_3662_ = lean_ctor_get_uint8(v_f_3659_, 2);
v_respectPseudoAlignment_3663_ = lean_ctor_get_uint8(v_f_3659_, 3);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_f_3659_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v_f_3659_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_dec(v_f_3659_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_3669_, 0, v_hardNestedFirstTerm_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3669_, 1, v_sparse_3661_);
lean_ctor_set_uint8(v_reuseFailAlloc_3669_, 2, v_parenthesize_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3669_, 3, v_respectPseudoAlignment_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object* v_terms_3671_, lean_object* v_format_3672_){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(v_format_3672_);
v___x_3674_ = l_Lean_Fmt_Layouts_application(v_terms_3671_, v___x_3673_);
lean_dec_ref(v___x_3673_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(lean_object* v_x_3675_){
_start:
{
if (lean_obj_tag(v_x_3675_) == 0)
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_unsigned_to_nat(0u);
return v___x_3676_;
}
else
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_unsigned_to_nat(1u);
return v___x_3677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___boxed(lean_object* v_x_3678_){
_start:
{
lean_object* v_res_3679_; 
v_res_3679_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(v_x_3678_);
lean_dec_ref(v_x_3678_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object* v_t_3680_, lean_object* v_k_3681_){
_start:
{
lean_object* v_doc_3682_; lean_object* v___x_3683_; 
v_doc_3682_ = lean_ctor_get(v_t_3680_, 0);
lean_inc_ref(v_doc_3682_);
lean_dec_ref(v_t_3680_);
v___x_3683_ = lean_apply_1(v_k_3681_, v_doc_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object* v_motive_3684_, lean_object* v_ctorIdx_3685_, lean_object* v_t_3686_, lean_object* v_h_3687_, lean_object* v_k_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3686_, v_k_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object* v_motive_3690_, lean_object* v_ctorIdx_3691_, lean_object* v_t_3692_, lean_object* v_h_3693_, lean_object* v_k_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(v_motive_3690_, v_ctorIdx_3691_, v_t_3692_, v_h_3693_, v_k_3694_);
lean_dec(v_ctorIdx_3691_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object* v_t_3696_, lean_object* v_sep_3697_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3696_, v_sep_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object* v_motive_3699_, lean_object* v_t_3700_, lean_object* v_h_3701_, lean_object* v_sep_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3700_, v_sep_3702_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object* v_t_3704_, lean_object* v_elems_3705_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3704_, v_elems_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object* v_motive_3707_, lean_object* v_t_3708_, lean_object* v_h_3709_, lean_object* v_elems_3710_){
_start:
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_3708_, v_elems_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t v_sz_3712_, size_t v_i_3713_, lean_object* v_bs_3714_){
_start:
{
uint8_t v___x_3715_; 
v___x_3715_ = lean_usize_dec_lt(v_i_3713_, v_sz_3712_);
if (v___x_3715_ == 0)
{
return v_bs_3714_;
}
else
{
lean_object* v_v_3716_; lean_object* v___x_3717_; lean_object* v_bs_x27_3718_; lean_object* v___y_3720_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v_v_3716_ = lean_array_uget(v_bs_3714_, v_i_3713_);
v___x_3717_ = lean_unsigned_to_nat(0u);
v_bs_x27_3718_ = lean_array_uset(v_bs_3714_, v_i_3713_, v___x_3717_);
v___x_3725_ = lean_usize_to_nat(v_i_3713_);
v___x_3726_ = lean_unsigned_to_nat(2u);
v___x_3727_ = lean_nat_mod(v___x_3725_, v___x_3726_);
lean_dec(v___x_3725_);
v___x_3728_ = lean_nat_dec_eq(v___x_3727_, v___x_3717_);
lean_dec(v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; 
v___x_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3729_, 0, v_v_3716_);
v___y_3720_ = v___x_3729_;
goto v___jp_3719_;
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3730_ = lean_unsigned_to_nat(1u);
v___x_3731_ = lean_mk_empty_array_with_capacity(v___x_3730_);
v___x_3732_ = lean_array_push(v___x_3731_, v_v_3716_);
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
v___y_3720_ = v___x_3733_;
goto v___jp_3719_;
}
v___jp_3719_:
{
size_t v___x_3721_; size_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = ((size_t)1ULL);
v___x_3722_ = lean_usize_add(v_i_3713_, v___x_3721_);
v___x_3723_ = lean_array_uset(v_bs_x27_3718_, v_i_3713_, v___y_3720_);
v_i_3713_ = v___x_3722_;
v_bs_3714_ = v___x_3723_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object* v_sz_3734_, lean_object* v_i_3735_, lean_object* v_bs_3736_){
_start:
{
size_t v_sz_boxed_3737_; size_t v_i_boxed_3738_; lean_object* v_res_3739_; 
v_sz_boxed_3737_ = lean_unbox_usize(v_sz_3734_);
lean_dec(v_sz_3734_);
v_i_boxed_3738_ = lean_unbox_usize(v_i_3735_);
lean_dec(v_i_3735_);
v_res_3739_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_boxed_3737_, v_i_boxed_3738_, v_bs_3736_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object* v_elems_3740_){
_start:
{
size_t v_sz_3741_; size_t v___x_3742_; lean_object* v___x_3743_; 
v_sz_3741_ = lean_array_size(v_elems_3740_);
v___x_3742_ = ((size_t)0ULL);
v___x_3743_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3741_, v___x_3742_, v_elems_3740_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object* v_s_3744_, lean_object* v_elems_3745_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_elems_3745_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object* v_s_3747_, lean_object* v_elems_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(v_s_3747_, v_elems_3748_);
lean_dec_ref(v_s_3747_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object* v_as_3750_, size_t v_sz_3751_, size_t v_i_3752_, lean_object* v_bs_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_3751_, v_i_3752_, v_bs_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object* v_as_3755_, lean_object* v_sz_3756_, lean_object* v_i_3757_, lean_object* v_bs_3758_){
_start:
{
size_t v_sz_boxed_3759_; size_t v_i_boxed_3760_; lean_object* v_res_3761_; 
v_sz_boxed_3759_ = lean_unbox_usize(v_sz_3756_);
lean_dec(v_sz_3756_);
v_i_boxed_3760_ = lean_unbox_usize(v_i_3757_);
lean_dec(v_i_3757_);
v_res_3761_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(v_as_3755_, v_sz_boxed_3759_, v_i_boxed_3760_, v_bs_3758_);
lean_dec_ref(v_as_3755_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t v_sz_3764_, size_t v_i_3765_, lean_object* v_bs_3766_){
_start:
{
uint8_t v___x_3767_; 
v___x_3767_ = lean_usize_dec_lt(v_i_3765_, v_sz_3764_);
if (v___x_3767_ == 0)
{
return v_bs_3766_;
}
else
{
lean_object* v_v_3768_; lean_object* v___x_3769_; lean_object* v_bs_x27_3770_; lean_object* v___y_3772_; 
v_v_3768_ = lean_array_uget(v_bs_3766_, v_i_3765_);
v___x_3769_ = lean_unsigned_to_nat(0u);
v_bs_x27_3770_ = lean_array_uset(v_bs_3766_, v_i_3765_, v___x_3769_);
if (lean_obj_tag(v_v_3768_) == 0)
{
v___y_3772_ = v_v_3768_;
goto v___jp_3771_;
}
else
{
lean_object* v_docs_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3799_; 
v_docs_3777_ = lean_ctor_get(v_v_3768_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_v_3768_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3779_ = v_v_3768_;
v_isShared_3780_ = v_isSharedCheck_3799_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_docs_3777_);
lean_dec(v_v_3768_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3799_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3781_ = lean_array_get_size(v_docs_3777_);
v___x_3782_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_3783_ = lean_nat_dec_lt(v___x_3769_, v___x_3781_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
lean_del_object(v___x_3779_);
lean_dec_ref(v_docs_3777_);
v___x_3784_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_3772_ = v___x_3784_;
goto v___jp_3771_;
}
else
{
uint8_t v___x_3785_; 
v___x_3785_ = lean_nat_dec_le(v___x_3781_, v___x_3781_);
if (v___x_3785_ == 0)
{
if (v___x_3783_ == 0)
{
lean_object* v___x_3786_; 
lean_del_object(v___x_3779_);
lean_dec_ref(v_docs_3777_);
v___x_3786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_3772_ = v___x_3786_;
goto v___jp_3771_;
}
else
{
size_t v___x_3787_; size_t v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3791_; 
v___x_3787_ = ((size_t)0ULL);
v___x_3788_ = lean_usize_of_nat(v___x_3781_);
v___x_3789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_docs_3777_, v___x_3787_, v___x_3788_, v___x_3782_);
lean_dec_ref(v_docs_3777_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3789_);
v___x_3791_ = v___x_3779_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
v___y_3772_ = v___x_3791_;
goto v___jp_3771_;
}
}
}
else
{
size_t v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3793_ = ((size_t)0ULL);
v___x_3794_ = lean_usize_of_nat(v___x_3781_);
v___x_3795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_docs_3777_, v___x_3793_, v___x_3794_, v___x_3782_);
lean_dec_ref(v_docs_3777_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3795_);
v___x_3797_ = v___x_3779_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
v___y_3772_ = v___x_3797_;
goto v___jp_3771_;
}
}
}
}
}
v___jp_3771_:
{
size_t v___x_3773_; size_t v___x_3774_; lean_object* v___x_3775_; 
v___x_3773_ = ((size_t)1ULL);
v___x_3774_ = lean_usize_add(v_i_3765_, v___x_3773_);
v___x_3775_ = lean_array_uset(v_bs_x27_3770_, v_i_3765_, v___y_3772_);
v_i_3765_ = v___x_3774_;
v_bs_3766_ = v___x_3775_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object* v_sz_3800_, lean_object* v_i_3801_, lean_object* v_bs_3802_){
_start:
{
size_t v_sz_boxed_3803_; size_t v_i_boxed_3804_; lean_object* v_res_3805_; 
v_sz_boxed_3803_ = lean_unbox_usize(v_sz_3800_);
lean_dec(v_sz_3800_);
v_i_boxed_3804_ = lean_unbox_usize(v_i_3801_);
lean_dec(v_i_3801_);
v_res_3805_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_boxed_3803_, v_i_boxed_3804_, v_bs_3802_);
return v_res_3805_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object* v_as_3806_, lean_object* v_j_3807_){
_start:
{
lean_object* v___x_3812_; uint8_t v___x_3813_; 
v___x_3812_ = lean_array_get_size(v_as_3806_);
v___x_3813_ = lean_nat_dec_lt(v_j_3807_, v___x_3812_);
if (v___x_3813_ == 0)
{
lean_object* v___x_3814_; 
lean_dec(v_j_3807_);
v___x_3814_ = lean_box(0);
return v___x_3814_;
}
else
{
lean_object* v___x_3815_; 
v___x_3815_ = lean_array_fget(v_as_3806_, v_j_3807_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_dec_ref_known(v___x_3815_, 1);
goto v___jp_3808_;
}
else
{
lean_object* v_docs_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3826_; 
v_docs_3816_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3818_ = v___x_3815_;
v_isShared_3819_ = v_isSharedCheck_3826_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_docs_3816_);
lean_dec(v___x_3815_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3826_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = lean_array_get_size(v_docs_3816_);
lean_dec_ref(v_docs_3816_);
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = lean_nat_dec_eq(v___x_3820_, v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3824_; 
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v_j_3807_);
v___x_3824_ = v___x_3818_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_j_3807_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
else
{
lean_del_object(v___x_3818_);
goto v___jp_3808_;
}
}
}
}
v___jp_3808_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = lean_unsigned_to_nat(1u);
v___x_3810_ = lean_nat_add(v_j_3807_, v___x_3809_);
lean_dec(v_j_3807_);
v_j_3807_ = v___x_3810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object* v_as_3827_, lean_object* v_j_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_as_3827_, v_j_3828_);
lean_dec_ref(v_as_3827_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t v_sz_3830_, size_t v_i_3831_, lean_object* v_bs_3832_){
_start:
{
uint8_t v___x_3833_; 
v___x_3833_ = lean_usize_dec_lt(v_i_3831_, v_sz_3830_);
if (v___x_3833_ == 0)
{
return v_bs_3832_;
}
else
{
lean_object* v_v_3834_; lean_object* v___x_3835_; lean_object* v_bs_x27_3836_; lean_object* v___y_3838_; 
v_v_3834_ = lean_array_uget(v_bs_3832_, v_i_3831_);
v___x_3835_ = lean_unsigned_to_nat(0u);
v_bs_x27_3836_ = lean_array_uset(v_bs_3832_, v_i_3831_, v___x_3835_);
if (lean_obj_tag(v_v_3834_) == 0)
{
lean_object* v_doc_3843_; 
v_doc_3843_ = lean_ctor_get(v_v_3834_, 0);
lean_inc_ref(v_doc_3843_);
lean_dec_ref_known(v_v_3834_, 1);
v___y_3838_ = v_doc_3843_;
goto v___jp_3837_;
}
else
{
lean_object* v_docs_3844_; lean_object* v___x_3845_; 
v_docs_3844_ = lean_ctor_get(v_v_3834_, 0);
lean_inc_ref(v_docs_3844_);
lean_dec_ref_known(v_v_3834_, 1);
v___x_3845_ = l_Lean_Fmt_Layouts_fill(v_docs_3844_);
lean_dec_ref(v_docs_3844_);
v___y_3838_ = v___x_3845_;
goto v___jp_3837_;
}
v___jp_3837_:
{
size_t v___x_3839_; size_t v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = ((size_t)1ULL);
v___x_3840_ = lean_usize_add(v_i_3831_, v___x_3839_);
v___x_3841_ = lean_array_uset(v_bs_x27_3836_, v_i_3831_, v___y_3838_);
v_i_3831_ = v___x_3840_;
v_bs_3832_ = v___x_3841_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object* v_sz_3846_, lean_object* v_i_3847_, lean_object* v_bs_3848_){
_start:
{
size_t v_sz_boxed_3849_; size_t v_i_boxed_3850_; lean_object* v_res_3851_; 
v_sz_boxed_3849_ = lean_unbox_usize(v_sz_3846_);
lean_dec(v_sz_3846_);
v_i_boxed_3850_ = lean_unbox_usize(v_i_3847_);
lean_dec(v_i_3847_);
v_res_3851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_boxed_3849_, v_i_boxed_3850_, v_bs_3848_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object* v_lb_3853_, lean_object* v_terms_3854_, lean_object* v_rb_3855_){
_start:
{
lean_object* v_terms_3857_; size_t v_sz_3865_; size_t v___x_3866_; lean_object* v_terms_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v_sz_3865_ = lean_array_size(v_terms_3854_);
v___x_3866_ = ((size_t)0ULL);
v_terms_3867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_3865_, v___x_3866_, v_terms_3854_);
v___x_3868_ = lean_unsigned_to_nat(1u);
v___x_3869_ = lean_array_get_size(v_terms_3867_);
v___x_3870_ = lean_nat_dec_lt(v___x_3868_, v___x_3869_);
if (v___x_3870_ == 0)
{
v_terms_3857_ = v_terms_3867_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3871_; lean_object* v_firstElemsIdx_x3f_3872_; 
v___x_3871_ = lean_unsigned_to_nat(0u);
v_firstElemsIdx_x3f_3872_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_terms_3867_, v___x_3871_);
if (lean_obj_tag(v_firstElemsIdx_x3f_3872_) == 1)
{
lean_object* v_val_3873_; uint8_t v___x_3874_; 
v_val_3873_ = lean_ctor_get(v_firstElemsIdx_x3f_3872_, 0);
lean_inc(v_val_3873_);
lean_dec_ref_known(v_firstElemsIdx_x3f_3872_, 1);
v___x_3874_ = lean_nat_dec_lt(v_val_3873_, v___x_3869_);
if (v___x_3874_ == 0)
{
lean_dec(v_val_3873_);
v_terms_3857_ = v_terms_3867_;
goto v___jp_3856_;
}
else
{
lean_object* v_v_3875_; lean_object* v___x_3876_; lean_object* v_xs_x27_3877_; lean_object* v___y_3879_; 
v_v_3875_ = lean_array_fget(v_terms_3867_, v_val_3873_);
v___x_3876_ = lean_box(0);
v_xs_x27_3877_ = lean_array_fset(v_terms_3867_, v_val_3873_, v___x_3876_);
if (lean_obj_tag(v_v_3875_) == 0)
{
v___y_3879_ = v_v_3875_;
goto v___jp_3878_;
}
else
{
lean_object* v_docs_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v_docs_3881_ = lean_ctor_get(v_v_3875_, 0);
v___x_3882_ = lean_array_get_size(v_docs_3881_);
v___x_3883_ = lean_nat_dec_lt(v___x_3871_, v___x_3882_);
if (v___x_3883_ == 0)
{
v___y_3879_ = v_v_3875_;
goto v___jp_3878_;
}
else
{
lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3894_; 
lean_inc_ref(v_docs_3881_);
v_isSharedCheck_3894_ = !lean_is_exclusive(v_v_3875_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; 
v_unused_3895_ = lean_ctor_get(v_v_3875_, 0);
lean_dec(v_unused_3895_);
v___x_3885_ = v_v_3875_;
v_isShared_3886_ = v_isSharedCheck_3894_;
goto v_resetjp_3884_;
}
else
{
lean_dec(v_v_3875_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3894_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v_v_3887_; lean_object* v_xs_x27_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3892_; 
v_v_3887_ = lean_array_fget(v_docs_3881_, v___x_3871_);
v_xs_x27_3888_ = lean_array_fset(v_docs_3881_, v___x_3871_, v___x_3876_);
v___x_3889_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3887_);
v___x_3890_ = lean_array_fset(v_xs_x27_3888_, v___x_3871_, v___x_3889_);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3890_);
v___x_3892_ = v___x_3885_;
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
v___y_3879_ = v___x_3892_;
goto v___jp_3878_;
}
}
}
}
v___jp_3878_:
{
lean_object* v___x_3880_; 
v___x_3880_ = lean_array_fset(v_xs_x27_3877_, v_val_3873_, v___y_3879_);
lean_dec(v_val_3873_);
v_terms_3857_ = v___x_3880_;
goto v___jp_3856_;
}
}
}
else
{
lean_dec(v_firstElemsIdx_x3f_3872_);
v_terms_3857_ = v_terms_3867_;
goto v___jp_3856_;
}
}
v___jp_3856_:
{
lean_object* v___x_3858_; size_t v_sz_3859_; size_t v___x_3860_; lean_object* v_terms_x27_3861_; lean_object* v_terms_x27_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3858_ = ((lean_object*)(l_Lean_Fmt_Layouts_metaApplication___closed__0));
v_sz_3859_ = lean_array_size(v_terms_3857_);
v___x_3860_ = ((size_t)0ULL);
v_terms_x27_3861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_3859_, v___x_3860_, v_terms_3857_);
v_terms_x27_3862_ = l_Lean_Fmt_Layouts_sepFill(v___x_3858_, v_terms_x27_3861_);
lean_dec_ref(v_terms_x27_3861_);
v___x_3863_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_3864_ = l_Lean_Fmt_Layouts_bracketed(v_lb_3853_, v_terms_x27_3862_, v_rb_3855_, v___x_3863_);
return v___x_3864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object* v_chain_3898_){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = ((lean_object*)(l_Lean_Fmt_Layouts_pipeOperator___closed__0));
v___x_3900_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_3898_, v___x_3899_);
return v___x_3900_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0(void){
_start:
{
uint8_t v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = 1;
v___x_3902_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3903_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set_uint8(v___x_3903_, sizeof(void*)*1, v___x_3901_);
return v___x_3903_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default(void){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_obj_once(&l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0, &l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0);
return v___x_3904_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock(void){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object* v_block_3906_){
_start:
{
uint8_t v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = 1;
v___x_3908_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3908_, 0, v_block_3906_);
lean_ctor_set_uint8(v___x_3908_, sizeof(void*)*1, v___x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object* v_val_3911_, uint8_t v___x_3912_, lean_object* v___x_3913_, lean_object* v_____r_3914_, lean_object* v_stickyAcc_3915_){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_3911_, v___x_3912_);
v___x_3917_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v___x_3913_, v_stickyAcc_3915_, v___x_3916_);
lean_dec(v___x_3916_);
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object* v_val_3919_, lean_object* v___x_3920_, lean_object* v___x_3921_, lean_object* v_____r_3922_, lean_object* v_stickyAcc_3923_){
_start:
{
uint8_t v___x_1732__boxed_3924_; lean_object* v_res_3925_; 
v___x_1732__boxed_3924_ = lean_unbox(v___x_3920_);
v_res_3925_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_3919_, v___x_1732__boxed_3924_, v___x_3921_, v_____r_3922_, v_stickyAcc_3923_);
lean_dec_ref(v_val_3919_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object* v_upperBound_3926_, lean_object* v___y_3927_, lean_object* v___x_3928_, lean_object* v_a_3929_, lean_object* v_b_3930_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = lean_nat_dec_lt(v_a_3929_, v_upperBound_3926_);
if (v___x_3931_ == 0)
{
lean_dec(v_a_3929_);
return v_b_3930_;
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v_block_3934_; uint8_t v_hardNestedIfFirst_3935_; lean_object* v___x_3936_; lean_object* v_a_3938_; lean_object* v___y_3942_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3932_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_3933_ = lean_array_get_borrowed(v___x_3932_, v___y_3927_, v_a_3929_);
v_block_3934_ = lean_ctor_get(v___x_3933_, 0);
v_hardNestedIfFirst_3935_ = lean_ctor_get_uint8(v___x_3933_, sizeof(void*)*1);
v___x_3936_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_b_3930_);
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v_b_3930_);
v___x_3946_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0);
v___x_3947_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3945_, v___x_3946_);
v___x_3948_ = lean_box(0);
lean_inc_ref_n(v_block_3934_, 2);
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_block_3934_);
v___x_3950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3948_);
lean_ctor_set(v___x_3950_, 1, v___x_3949_);
lean_ctor_set(v___x_3950_, 2, v___x_3948_);
v___x_3951_ = lean_unsigned_to_nat(2u);
v___x_3952_ = lean_mk_empty_array_with_capacity(v___x_3951_);
lean_inc_ref(v___x_3952_);
v___x_3953_ = lean_array_push(v___x_3952_, v___x_3947_);
v___x_3954_ = lean_array_push(v___x_3953_, v___x_3950_);
v___x_3955_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3954_);
lean_dec_ref(v___x_3954_);
v___x_3956_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3955_);
v___x_3957_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_block_3934_);
if (lean_obj_tag(v___x_3957_) == 1)
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3982_; 
v_val_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_3982_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3982_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_stickyVariant_3962_; lean_object* v___x_3963_; lean_object* v___x_3965_; 
v_stickyVariant_3962_ = lean_ctor_get(v_val_3958_, 0);
v___x_3963_ = l_Lean_Fmt_TaggedDoc_flattened(v_b_3930_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3963_);
v___x_3965_ = v___x_3960_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3963_);
v___x_3965_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_3967_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3965_, v___x_3966_);
lean_inc_ref(v_stickyVariant_3962_);
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v_stickyVariant_3962_);
v___x_3969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3948_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
lean_ctor_set(v___x_3969_, 2, v___x_3948_);
v___x_3970_ = lean_array_push(v___x_3952_, v___x_3967_);
v___x_3971_ = lean_array_push(v___x_3970_, v___x_3969_);
v___x_3972_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3971_);
lean_dec_ref(v___x_3971_);
if (v_hardNestedIfFirst_3935_ == 0)
{
goto v___jp_3973_;
}
else
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = lean_nat_sub(v___x_3928_, v___x_3936_);
v___x_3977_ = lean_nat_dec_lt(v_a_3929_, v___x_3976_);
lean_dec(v___x_3976_);
if (v___x_3977_ == 0)
{
goto v___jp_3973_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_3972_);
v___x_3979_ = lean_box(0);
v___x_3980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_3958_, v___x_3931_, v___x_3956_, v___x_3979_, v___x_3978_);
lean_dec(v_val_3958_);
v___y_3942_ = v___x_3980_;
goto v___jp_3941_;
}
}
v___jp_3973_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_box(0);
v___x_3975_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_3958_, v___x_3931_, v___x_3956_, v___x_3974_, v___x_3972_);
lean_dec(v_val_3958_);
v___y_3942_ = v___x_3975_;
goto v___jp_3941_;
}
}
}
}
else
{
lean_dec(v___x_3957_);
lean_dec_ref(v___x_3952_);
lean_dec_ref(v_b_3930_);
v_a_3938_ = v___x_3956_;
goto v___jp_3937_;
}
v___jp_3937_:
{
lean_object* v___x_3939_; 
v___x_3939_ = lean_nat_add(v_a_3929_, v___x_3936_);
lean_dec(v_a_3929_);
v_a_3929_ = v___x_3939_;
v_b_3930_ = v_a_3938_;
goto _start;
}
v___jp_3941_:
{
if (lean_obj_tag(v___y_3942_) == 0)
{
lean_object* v_a_3943_; 
lean_dec(v_a_3929_);
v_a_3943_ = lean_ctor_get(v___y_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___y_3942_, 1);
return v_a_3943_;
}
else
{
lean_object* v_a_3944_; 
v_a_3944_ = lean_ctor_get(v___y_3942_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___y_3942_, 1);
v_a_3938_ = v_a_3944_;
goto v___jp_3937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object* v_upperBound_3983_, lean_object* v___y_3984_, lean_object* v___x_3985_, lean_object* v_a_3986_, lean_object* v_b_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_3983_, v___y_3984_, v___x_3985_, v_a_3986_, v_b_3987_);
lean_dec(v___x_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v_upperBound_3983_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object* v_as_3989_, size_t v_i_3990_, size_t v_stop_3991_, lean_object* v_b_3992_){
_start:
{
lean_object* v___y_3994_; uint8_t v___x_3998_; 
v___x_3998_ = lean_usize_dec_eq(v_i_3990_, v_stop_3991_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v_block_4000_; uint8_t v___x_4001_; 
v___x_3999_ = lean_array_uget_borrowed(v_as_3989_, v_i_3990_);
v_block_4000_ = lean_ctor_get(v___x_3999_, 0);
v___x_4001_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_block_4000_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; 
lean_inc(v___x_3999_);
v___x_4002_ = lean_array_push(v_b_3992_, v___x_3999_);
v___y_3994_ = v___x_4002_;
goto v___jp_3993_;
}
else
{
v___y_3994_ = v_b_3992_;
goto v___jp_3993_;
}
}
else
{
return v_b_3992_;
}
v___jp_3993_:
{
size_t v___x_3995_; size_t v___x_3996_; 
v___x_3995_ = ((size_t)1ULL);
v___x_3996_ = lean_usize_add(v_i_3990_, v___x_3995_);
v_i_3990_ = v___x_3996_;
v_b_3992_ = v___y_3994_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object* v_as_4003_, lean_object* v_i_4004_, lean_object* v_stop_4005_, lean_object* v_b_4006_){
_start:
{
size_t v_i_boxed_4007_; size_t v_stop_boxed_4008_; lean_object* v_res_4009_; 
v_i_boxed_4007_ = lean_unbox_usize(v_i_4004_);
lean_dec(v_i_4004_);
v_stop_boxed_4008_ = lean_unbox_usize(v_stop_4005_);
lean_dec(v_stop_4005_);
v_res_4009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_as_4003_, v_i_boxed_4007_, v_stop_boxed_4008_, v_b_4006_);
lean_dec_ref(v_as_4003_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object* v_blocks_4012_, uint8_t v_format_4013_){
_start:
{
lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___x_4021_; lean_object* v___y_4023_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4021_ = lean_unsigned_to_nat(0u);
v___x_4034_ = lean_array_get_size(v_blocks_4012_);
v___x_4035_ = ((lean_object*)(l_Lean_Fmt_Layouts_blocks___closed__0));
v___x_4036_ = lean_nat_dec_lt(v___x_4021_, v___x_4034_);
if (v___x_4036_ == 0)
{
v___y_4023_ = v___x_4035_;
goto v___jp_4022_;
}
else
{
uint8_t v___x_4037_; 
v___x_4037_ = lean_nat_dec_le(v___x_4034_, v___x_4034_);
if (v___x_4037_ == 0)
{
if (v___x_4036_ == 0)
{
v___y_4023_ = v___x_4035_;
goto v___jp_4022_;
}
else
{
size_t v___x_4038_; size_t v___x_4039_; lean_object* v___x_4040_; 
v___x_4038_ = ((size_t)0ULL);
v___x_4039_ = lean_usize_of_nat(v___x_4034_);
v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4012_, v___x_4038_, v___x_4039_, v___x_4035_);
v___y_4023_ = v___x_4040_;
goto v___jp_4022_;
}
}
else
{
size_t v___x_4041_; size_t v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = ((size_t)0ULL);
v___x_4042_ = lean_usize_of_nat(v___x_4034_);
v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4012_, v___x_4041_, v___x_4042_, v___x_4035_);
v___y_4023_ = v___x_4043_;
goto v___jp_4022_;
}
}
v___jp_4014_:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v___y_4015_, v___y_4017_, v___y_4015_, v___y_4016_, v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4015_);
if (v_format_4013_ == 0)
{
return v___x_4019_;
}
else
{
lean_object* v___x_4020_; 
v___x_4020_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4019_);
return v___x_4020_;
}
}
v___jp_4022_:
{
lean_object* v___x_4024_; uint8_t v___x_4025_; 
v___x_4024_ = lean_array_get_size(v___y_4023_);
v___x_4025_ = lean_nat_dec_eq(v___x_4024_, v___x_4021_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v_block_4028_; uint8_t v_hardNestedIfFirst_4029_; lean_object* v___x_4030_; uint8_t v___x_4031_; 
v___x_4026_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4027_ = lean_array_get_borrowed(v___x_4026_, v___y_4023_, v___x_4021_);
v_block_4028_ = lean_ctor_get(v___x_4027_, 0);
v_hardNestedIfFirst_4029_ = lean_ctor_get_uint8(v___x_4027_, sizeof(void*)*1);
v___x_4030_ = lean_unsigned_to_nat(1u);
v___x_4031_ = lean_nat_dec_eq(v___x_4024_, v___x_4030_);
if (v___x_4031_ == 0)
{
if (v_hardNestedIfFirst_4029_ == 0)
{
lean_inc_ref(v_block_4028_);
v___y_4015_ = v___x_4024_;
v___y_4016_ = v___x_4030_;
v___y_4017_ = v___y_4023_;
v___y_4018_ = v_block_4028_;
goto v___jp_4014_;
}
else
{
lean_object* v___x_4032_; 
lean_inc_ref(v_block_4028_);
v___x_4032_ = l_Lean_Fmt_TaggedDoc_hardNested(v_block_4028_);
v___y_4015_ = v___x_4024_;
v___y_4016_ = v___x_4030_;
v___y_4017_ = v___y_4023_;
v___y_4018_ = v___x_4032_;
goto v___jp_4014_;
}
}
else
{
lean_inc_ref(v_block_4028_);
lean_dec_ref(v___y_4023_);
return v_block_4028_;
}
}
else
{
lean_object* v___x_4033_; 
lean_dec_ref(v___y_4023_);
v___x_4033_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_4033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object* v_blocks_4044_, lean_object* v_format_4045_){
_start:
{
uint8_t v_format_boxed_4046_; lean_object* v_res_4047_; 
v_format_boxed_4046_ = lean_unbox(v_format_4045_);
v_res_4047_ = l_Lean_Fmt_Layouts_blocks(v_blocks_4044_, v_format_boxed_4046_);
lean_dec_ref(v_blocks_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object* v_upperBound_4048_, lean_object* v___y_4049_, lean_object* v___x_4050_, lean_object* v_inst_4051_, lean_object* v_R_4052_, lean_object* v_a_4053_, lean_object* v_b_4054_, lean_object* v_c_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4048_, v___y_4049_, v___x_4050_, v_a_4053_, v_b_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object* v_upperBound_4057_, lean_object* v___y_4058_, lean_object* v___x_4059_, lean_object* v_inst_4060_, lean_object* v_R_4061_, lean_object* v_a_4062_, lean_object* v_b_4063_, lean_object* v_c_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(v_upperBound_4057_, v___y_4058_, v___x_4059_, v_inst_4060_, v_R_4061_, v_a_4062_, v_b_4063_, v_c_4064_);
lean_dec(v___x_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v_upperBound_4057_);
return v_res_4065_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_tuple___closed__0(void){
_start:
{
uint8_t v___x_4066_; uint8_t v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4066_ = 0;
v___x_4067_ = 1;
v___x_4068_ = l_Lean_Fmt_TaggedDoc_break;
v___x_4069_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*1, v___x_4067_);
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*1 + 1, v___x_4066_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object* v_sep_4070_, lean_object* v_lb_4071_, lean_object* v_fields_4072_, lean_object* v_rb_4073_){
_start:
{
uint8_t v___x_4074_; lean_object* v_fields_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v___x_4074_ = 1;
lean_inc_ref(v_sep_4070_);
v_fields_4075_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4070_, v_fields_4072_, v___x_4074_);
v___x_4076_ = lean_array_get_size(v_fields_4075_);
v___x_4077_ = lean_unsigned_to_nat(1u);
v___x_4078_ = lean_nat_dec_eq(v___x_4076_, v___x_4077_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; lean_object* v_fields_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4079_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v_fields_4080_ = l_Lean_Fmt_Layouts_sepArray(v_sep_4070_, v_fields_4075_, v___x_4079_);
lean_dec_ref(v_fields_4075_);
v___x_4081_ = lean_obj_once(&l_Lean_Fmt_Layouts_tuple___closed__0, &l_Lean_Fmt_Layouts_tuple___closed__0_once, _init_l_Lean_Fmt_Layouts_tuple___closed__0);
v___x_4082_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4071_, v_fields_4080_, v_rb_4073_, v___x_4081_);
return v___x_4082_;
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec_ref(v_sep_4070_);
v___x_4083_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4084_ = lean_unsigned_to_nat(0u);
v___x_4085_ = lean_array_get(v___x_4083_, v_fields_4075_, v___x_4084_);
lean_dec_ref(v_fields_4075_);
v___x_4086_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4087_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4071_, v___x_4085_, v_rb_4073_, v___x_4086_);
return v___x_4087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object* v_sep_4088_, lean_object* v_lb_4089_, lean_object* v_fields_4090_, lean_object* v_rb_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_Fmt_Layouts_tuple(v_sep_4088_, v_lb_4089_, v_fields_4090_, v_rb_4091_);
lean_dec_ref(v_fields_4090_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object* v_sep_4093_, lean_object* v_lb_4094_, lean_object* v_elems_4095_, lean_object* v_rb_4096_, lean_object* v_format_4097_){
_start:
{
uint8_t v_spacing_4098_; uint8_t v_unindentedRb_4099_; uint8_t v___x_4100_; lean_object* v_elems_4101_; lean_object* v___y_4103_; 
v_spacing_4098_ = lean_ctor_get_uint8(v_format_4097_, 0);
v_unindentedRb_4099_ = lean_ctor_get_uint8(v_format_4097_, 1);
v___x_4100_ = 1;
lean_inc_ref(v_sep_4093_);
v_elems_4101_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4093_, v_elems_4095_, v___x_4100_);
if (v_spacing_4098_ == 0)
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_Fmt_TaggedDoc_break;
v___y_4103_ = v___x_4108_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4103_ = v___x_4109_;
goto v___jp_4102_;
}
v___jp_4102_:
{
lean_object* v_fields_4104_; uint8_t v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v_fields_4104_ = l_Lean_Fmt_Layouts_sepFill(v_sep_4093_, v_elems_4101_);
lean_dec_ref(v_elems_4101_);
v___x_4105_ = 1;
lean_inc_ref(v___y_4103_);
v___x_4106_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4106_, 0, v___y_4103_);
lean_ctor_set_uint8(v___x_4106_, sizeof(void*)*1, v_unindentedRb_4099_);
lean_ctor_set_uint8(v___x_4106_, sizeof(void*)*1 + 1, v___x_4105_);
v___x_4107_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4094_, v_fields_4104_, v_rb_4096_, v___x_4106_);
return v___x_4107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object* v_sep_4110_, lean_object* v_lb_4111_, lean_object* v_elems_4112_, lean_object* v_rb_4113_, lean_object* v_format_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Fmt_Layouts_collection(v_sep_4110_, v_lb_4111_, v_elems_4112_, v_rb_4113_, v_format_4114_);
lean_dec_ref(v_format_4114_);
lean_dec_ref(v_elems_4112_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(uint8_t v_x_4116_){
_start:
{
if (v_x_4116_ == 0)
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_unsigned_to_nat(0u);
return v___x_4117_;
}
else
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_unsigned_to_nat(1u);
return v___x_4118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___boxed(lean_object* v_x_4119_){
_start:
{
uint8_t v_x_boxed_4120_; lean_object* v_res_4121_; 
v_x_boxed_4120_ = lean_unbox(v_x_4119_);
v_res_4121_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(v_x_boxed_4120_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object* v_k_4122_){
_start:
{
lean_inc(v_k_4122_);
return v_k_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object* v_k_4123_){
_start:
{
lean_object* v_res_4124_; 
v_res_4124_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_k_4123_);
lean_dec(v_k_4123_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object* v_motive_4125_, lean_object* v_ctorIdx_4126_, uint8_t v_t_4127_, lean_object* v_h_4128_, lean_object* v_k_4129_){
_start:
{
lean_inc(v_k_4129_);
return v_k_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object* v_motive_4130_, lean_object* v_ctorIdx_4131_, lean_object* v_t_4132_, lean_object* v_h_4133_, lean_object* v_k_4134_){
_start:
{
uint8_t v_t_boxed_4135_; lean_object* v_res_4136_; 
v_t_boxed_4135_ = lean_unbox(v_t_4132_);
v_res_4136_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(v_motive_4130_, v_ctorIdx_4131_, v_t_boxed_4135_, v_h_4133_, v_k_4134_);
lean_dec(v_k_4134_);
lean_dec(v_ctorIdx_4131_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object* v_local_4137_){
_start:
{
lean_inc(v_local_4137_);
return v_local_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object* v_local_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(v_local_4138_);
lean_dec(v_local_4138_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object* v_motive_4140_, uint8_t v_t_4141_, lean_object* v_h_4142_, lean_object* v_local_4143_){
_start:
{
lean_inc(v_local_4143_);
return v_local_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object* v_motive_4144_, lean_object* v_t_4145_, lean_object* v_h_4146_, lean_object* v_local_4147_){
_start:
{
uint8_t v_t_boxed_4148_; lean_object* v_res_4149_; 
v_t_boxed_4148_ = lean_unbox(v_t_4145_);
v_res_4149_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(v_motive_4144_, v_t_boxed_4148_, v_h_4146_, v_local_4147_);
lean_dec(v_local_4147_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object* v_global_4150_){
_start:
{
lean_inc(v_global_4150_);
return v_global_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object* v_global_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(v_global_4151_);
lean_dec(v_global_4151_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object* v_motive_4153_, uint8_t v_t_4154_, lean_object* v_h_4155_, lean_object* v_global_4156_){
_start:
{
lean_inc(v_global_4156_);
return v_global_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object* v_motive_4157_, lean_object* v_t_4158_, lean_object* v_h_4159_, lean_object* v_global_4160_){
_start:
{
uint8_t v_t_boxed_4161_; lean_object* v_res_4162_; 
v_t_boxed_4161_ = lean_unbox(v_t_4158_);
v_res_4162_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(v_motive_4157_, v_t_boxed_4161_, v_h_4159_, v_global_4160_);
lean_dec(v_global_4160_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(size_t v_sz_4163_, size_t v_i_4164_, lean_object* v_bs_4165_){
_start:
{
uint8_t v___x_4166_; 
v___x_4166_ = lean_usize_dec_lt(v_i_4164_, v_sz_4163_);
if (v___x_4166_ == 0)
{
return v_bs_4165_;
}
else
{
lean_object* v_v_4167_; lean_object* v___x_4168_; lean_object* v_bs_x27_4169_; lean_object* v___x_4170_; size_t v___x_4171_; size_t v___x_4172_; lean_object* v___x_4173_; 
v_v_4167_ = lean_array_uget(v_bs_4165_, v_i_4164_);
v___x_4168_ = lean_unsigned_to_nat(0u);
v_bs_x27_4169_ = lean_array_uset(v_bs_4165_, v_i_4164_, v___x_4168_);
v___x_4170_ = l_Lean_Fmt_Layouts_fill(v_v_4167_);
lean_dec(v_v_4167_);
v___x_4171_ = ((size_t)1ULL);
v___x_4172_ = lean_usize_add(v_i_4164_, v___x_4171_);
v___x_4173_ = lean_array_uset(v_bs_x27_4169_, v_i_4164_, v___x_4170_);
v_i_4164_ = v___x_4172_;
v_bs_4165_ = v___x_4173_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object* v_sz_4175_, lean_object* v_i_4176_, lean_object* v_bs_4177_){
_start:
{
size_t v_sz_boxed_4178_; size_t v_i_boxed_4179_; lean_object* v_res_4180_; 
v_sz_boxed_4178_ = lean_unbox_usize(v_sz_4175_);
lean_dec(v_sz_4175_);
v_i_boxed_4179_ = lean_unbox_usize(v_i_4176_);
lean_dec(v_i_4176_);
v_res_4180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_sz_boxed_4178_, v_i_boxed_4179_, v_bs_4177_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object* v_lvals_4181_, lean_object* v_binderGroups_4182_, lean_object* v_typeAscriptionTk_4183_, lean_object* v_type_4184_, uint8_t v_kind_4185_, lean_object* v_lvalsLayout_4186_){
_start:
{
uint8_t v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4203_; lean_object* v___y_4204_; lean_object* v___x_4209_; lean_object* v___y_4211_; lean_object* v___y_4221_; uint8_t v___y_4222_; lean_object* v___y_4224_; uint8_t v___y_4225_; lean_object* v___y_4230_; lean_object* v___x_4235_; lean_object* v___x_4236_; uint8_t v___x_4237_; 
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4235_ = lean_array_get_size(v_lvals_4181_);
v___x_4236_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4237_ = lean_nat_dec_lt(v___x_4209_, v___x_4235_);
if (v___x_4237_ == 0)
{
v___y_4230_ = v___x_4236_;
goto v___jp_4229_;
}
else
{
uint8_t v___x_4238_; 
v___x_4238_ = lean_nat_dec_le(v___x_4235_, v___x_4235_);
if (v___x_4238_ == 0)
{
if (v___x_4237_ == 0)
{
v___y_4230_ = v___x_4236_;
goto v___jp_4229_;
}
else
{
size_t v___x_4239_; size_t v___x_4240_; lean_object* v___x_4241_; 
v___x_4239_ = ((size_t)0ULL);
v___x_4240_ = lean_usize_of_nat(v___x_4235_);
v___x_4241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_lvals_4181_, v___x_4239_, v___x_4240_, v___x_4236_);
v___y_4230_ = v___x_4241_;
goto v___jp_4229_;
}
}
else
{
size_t v___x_4242_; size_t v___x_4243_; lean_object* v___x_4244_; 
v___x_4242_ = ((size_t)0ULL);
v___x_4243_ = lean_usize_of_nat(v___x_4235_);
v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__5_spec__5(v_lvals_4181_, v___x_4242_, v___x_4243_, v___x_4236_);
v___y_4230_ = v___x_4244_;
goto v___jp_4229_;
}
}
v___jp_4187_:
{
size_t v_sz_4191_; size_t v___x_4192_; lean_object* v_binderGroups_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v_sz_4191_ = lean_array_size(v_binderGroups_4182_);
v___x_4192_ = ((size_t)0ULL);
v_binderGroups_4193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_sz_4191_, v___x_4192_, v_binderGroups_4182_);
v___x_4194_ = lean_apply_1(v_lvalsLayout_4186_, v___y_4189_);
v___x_4195_ = lean_unsigned_to_nat(1u);
v___x_4196_ = lean_mk_empty_array_with_capacity(v___x_4195_);
v___x_4197_ = lean_array_push(v___x_4196_, v___x_4194_);
v___x_4198_ = l_Array_append___redArg(v___x_4197_, v_binderGroups_4193_);
lean_dec_ref(v_binderGroups_4193_);
v___x_4199_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4198_, v___y_4188_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = l_Lean_Fmt_Layouts_typeAscription(v___x_4199_, v_typeAscriptionTk_4183_, v_type_4184_, v___y_4190_);
lean_dec_ref(v___y_4190_);
v___x_4201_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4200_);
return v___x_4201_;
}
v___jp_4202_:
{
if (v_kind_4185_ == 0)
{
uint8_t v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = 0;
v___x_4206_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4206_, 0, v___x_4205_);
lean_ctor_set_uint8(v___x_4206_, 1, v___x_4205_);
lean_ctor_set_uint8(v___x_4206_, 2, v___y_4203_);
v___y_4188_ = v___y_4203_;
v___y_4189_ = v___y_4204_;
v___y_4190_ = v___x_4206_;
goto v___jp_4187_;
}
else
{
uint8_t v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = 0;
v___x_4208_ = lean_alloc_ctor(1, 0, 3);
lean_ctor_set_uint8(v___x_4208_, 0, v___x_4207_);
lean_ctor_set_uint8(v___x_4208_, 1, v___x_4207_);
lean_ctor_set_uint8(v___x_4208_, 2, v___y_4203_);
v___y_4188_ = v___y_4203_;
v___y_4189_ = v___y_4204_;
v___y_4190_ = v___x_4208_;
goto v___jp_4187_;
}
}
v___jp_4210_:
{
uint8_t v___x_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; 
v___x_4212_ = 1;
v___x_4213_ = lean_array_get_size(v___y_4211_);
v___x_4214_ = lean_nat_dec_lt(v___x_4209_, v___x_4213_);
if (v___x_4214_ == 0)
{
v___y_4203_ = v___x_4212_;
v___y_4204_ = v___y_4211_;
goto v___jp_4202_;
}
else
{
lean_object* v_v_4215_; lean_object* v___x_4216_; lean_object* v_xs_x27_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v_v_4215_ = lean_array_fget(v___y_4211_, v___x_4209_);
v___x_4216_ = lean_box(0);
v_xs_x27_4217_ = lean_array_fset(v___y_4211_, v___x_4209_, v___x_4216_);
v___x_4218_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4215_);
v___x_4219_ = lean_array_fset(v_xs_x27_4217_, v___x_4209_, v___x_4218_);
v___y_4203_ = v___x_4212_;
v___y_4204_ = v___x_4219_;
goto v___jp_4202_;
}
}
v___jp_4220_:
{
if (v___y_4222_ == 0)
{
v___y_4211_ = v___y_4221_;
goto v___jp_4210_;
}
else
{
v___y_4203_ = v___y_4222_;
v___y_4204_ = v___y_4221_;
goto v___jp_4202_;
}
}
v___jp_4223_:
{
if (v___y_4225_ == 0)
{
v___y_4211_ = v___y_4224_;
goto v___jp_4210_;
}
else
{
uint8_t v___x_4226_; 
v___x_4226_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_typeAscriptionTk_4183_);
if (v___x_4226_ == 0)
{
v___y_4221_ = v___y_4224_;
v___y_4222_ = v___x_4226_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4227_; uint8_t v___x_4228_; 
v___x_4227_ = lean_array_get_size(v_binderGroups_4182_);
v___x_4228_ = lean_nat_dec_eq(v___x_4227_, v___x_4209_);
v___y_4221_ = v___y_4224_;
v___y_4222_ = v___x_4228_;
goto v___jp_4220_;
}
}
}
v___jp_4229_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; uint8_t v___x_4233_; 
v___x_4231_ = lean_array_get_size(v___y_4230_);
v___x_4232_ = lean_unsigned_to_nat(1u);
v___x_4233_ = lean_nat_dec_le(v___x_4231_, v___x_4232_);
if (v___x_4233_ == 0)
{
v___y_4224_ = v___y_4230_;
v___y_4225_ = v___x_4233_;
goto v___jp_4223_;
}
else
{
uint8_t v___x_4234_; 
v___x_4234_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_type_4184_);
v___y_4224_ = v___y_4230_;
v___y_4225_ = v___x_4234_;
goto v___jp_4223_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object* v_lvals_4245_, lean_object* v_binderGroups_4246_, lean_object* v_typeAscriptionTk_4247_, lean_object* v_type_4248_, lean_object* v_kind_4249_, lean_object* v_lvalsLayout_4250_){
_start:
{
uint8_t v_kind_boxed_4251_; lean_object* v_res_4252_; 
v_kind_boxed_4251_ = lean_unbox(v_kind_4249_);
v_res_4252_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4245_, v_binderGroups_4246_, v_typeAscriptionTk_4247_, v_type_4248_, v_kind_boxed_4251_, v_lvalsLayout_4250_);
lean_dec_ref(v_lvals_4245_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(lean_object* v_terms_4253_){
_start:
{
uint8_t v___x_4254_; lean_object* v___x_4255_; 
v___x_4254_ = 1;
v___x_4255_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4253_, v___x_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object* v_terms_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_Fmt_Layouts_localSignature___lam__0(v_terms_4256_);
lean_dec_ref(v_terms_4256_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object* v_lvals_4259_, lean_object* v_binderGroups_4260_, lean_object* v_typeAscriptionTk_4261_, lean_object* v_type_4262_){
_start:
{
lean_object* v___f_4263_; uint8_t v___x_4264_; lean_object* v___x_4265_; 
v___f_4263_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4264_ = 0;
v___x_4265_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4259_, v_binderGroups_4260_, v_typeAscriptionTk_4261_, v_type_4262_, v___x_4264_, v___f_4263_);
return v___x_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object* v_lvals_4266_, lean_object* v_binderGroups_4267_, lean_object* v_typeAscriptionTk_4268_, lean_object* v_type_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_Fmt_Layouts_localSignature(v_lvals_4266_, v_binderGroups_4267_, v_typeAscriptionTk_4268_, v_type_4269_);
lean_dec_ref(v_lvals_4266_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object* v_lvals_4271_, lean_object* v_binderGroups_4272_, lean_object* v_typeAscriptionTk_4273_, lean_object* v_type_4274_){
_start:
{
lean_object* v___f_4275_; uint8_t v___x_4276_; lean_object* v___x_4277_; 
v___f_4275_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4276_ = 1;
v___x_4277_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4271_, v_binderGroups_4272_, v_typeAscriptionTk_4273_, v_type_4274_, v___x_4276_, v___f_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object* v_lvals_4278_, lean_object* v_binderGroups_4279_, lean_object* v_typeAscriptionTk_4280_, lean_object* v_type_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_Fmt_Layouts_globalSignature(v_lvals_4278_, v_binderGroups_4279_, v_typeAscriptionTk_4280_, v_type_4281_);
lean_dec_ref(v_lvals_4278_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object* v_signature_4283_, lean_object* v_separationTk_4284_, lean_object* v_body_4285_, uint8_t v_sticky_4286_){
_start:
{
uint8_t v___y_4288_; lean_object* v___y_4289_; uint8_t v___y_4330_; uint8_t v___x_4346_; 
v___x_4346_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_separationTk_4284_);
if (v___x_4346_ == 0)
{
v___y_4330_ = v___x_4346_;
goto v___jp_4329_;
}
else
{
uint8_t v___x_4347_; 
v___x_4347_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4285_);
v___y_4330_ = v___x_4347_;
goto v___jp_4329_;
}
v___jp_4287_:
{
lean_object* v_doc_4290_; 
v_doc_4290_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___y_4289_);
if (v_sticky_4286_ == 0)
{
lean_dec_ref(v_body_4285_);
lean_dec_ref(v_separationTk_4284_);
lean_dec_ref(v_signature_4283_);
return v_doc_4290_;
}
else
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v_lhs_4302_; lean_object* v___x_4303_; 
v___x_4291_ = l_Lean_Fmt_TaggedDoc_flattened(v_signature_4283_);
v___x_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4291_);
v___x_4293_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4294_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4292_, v___x_4293_);
v___x_4295_ = lean_box(0);
v___x_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4296_, 0, v_separationTk_4284_);
v___x_4297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
lean_ctor_set(v___x_4297_, 2, v___x_4295_);
v___x_4298_ = lean_unsigned_to_nat(2u);
v___x_4299_ = lean_mk_empty_array_with_capacity(v___x_4298_);
lean_inc_ref(v___x_4299_);
v___x_4300_ = lean_array_push(v___x_4299_, v___x_4294_);
v___x_4301_ = lean_array_push(v___x_4300_, v___x_4297_);
v_lhs_4302_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4301_);
lean_dec_ref(v___x_4301_);
lean_inc_ref(v_body_4285_);
v___x_4303_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_body_4285_);
if (lean_obj_tag(v___x_4303_) == 1)
{
lean_object* v_val_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4324_; 
v_val_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4324_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_val_4304_);
lean_dec(v___x_4303_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4324_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
uint8_t v_kind_4308_; 
v_kind_4308_ = lean_ctor_get_uint8(v_val_4304_, sizeof(void*)*1);
if (v_kind_4308_ == 1)
{
lean_object* v_stickyVariant_4309_; lean_object* v___x_4311_; 
lean_dec_ref(v_body_4285_);
v_stickyVariant_4309_ = lean_ctor_get(v_val_4304_, 0);
lean_inc_ref(v_stickyVariant_4309_);
lean_dec(v_val_4304_);
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 0, v_lhs_4302_);
v___x_4311_ = v___x_4306_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_lhs_4302_);
v___x_4311_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4312_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
v___x_4313_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4311_, v___x_4312_);
v___x_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4314_, 0, v_stickyVariant_4309_);
v___x_4315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4295_);
lean_ctor_set(v___x_4315_, 1, v___x_4314_);
lean_ctor_set(v___x_4315_, 2, v___x_4295_);
v___x_4316_ = lean_array_push(v___x_4299_, v___x_4313_);
v___x_4317_ = lean_array_push(v___x_4316_, v___x_4315_);
v___x_4318_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4317_);
lean_dec_ref(v___x_4317_);
v___x_4319_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4290_, v___x_4318_, v_kind_4308_);
return v___x_4319_;
}
}
else
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
lean_del_object(v___x_4306_);
lean_dec(v_val_4304_);
lean_dec_ref(v___x_4299_);
v___x_4321_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4322_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4302_, v___x_4321_, v_body_4285_, v___y_4288_);
v___x_4323_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4290_, v___x_4322_, v_kind_4308_);
return v___x_4323_;
}
}
}
else
{
lean_object* v___x_4325_; lean_object* v___x_4326_; uint8_t v___x_4327_; lean_object* v___x_4328_; 
lean_dec(v___x_4303_);
lean_dec_ref(v___x_4299_);
v___x_4325_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4326_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4302_, v___x_4325_, v_body_4285_, v___y_4288_);
v___x_4327_ = 0;
v___x_4328_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4290_, v___x_4326_, v___x_4327_);
return v___x_4328_;
}
}
}
v___jp_4329_:
{
uint8_t v___x_4331_; 
v___x_4331_ = 1;
if (v___y_4330_ == 0)
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v_lhs_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_inc_ref(v_signature_4283_);
v___x_4332_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4283_);
v___x_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
v___x_4334_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4335_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4333_, v___x_4334_);
v___x_4336_ = lean_box(0);
lean_inc_ref(v_separationTk_4284_);
v___x_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4337_, 0, v_separationTk_4284_);
v___x_4338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
lean_ctor_set(v___x_4338_, 2, v___x_4336_);
v___x_4339_ = lean_unsigned_to_nat(2u);
v___x_4340_ = lean_mk_empty_array_with_capacity(v___x_4339_);
v___x_4341_ = lean_array_push(v___x_4340_, v___x_4335_);
v___x_4342_ = lean_array_push(v___x_4341_, v___x_4338_);
v_lhs_4343_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4342_);
lean_dec_ref(v___x_4342_);
v___x_4344_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_body_4285_);
v___x_4345_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4343_, v___x_4344_, v_body_4285_, v___x_4331_);
v___y_4288_ = v___x_4331_;
v___y_4289_ = v___x_4345_;
goto v___jp_4287_;
}
else
{
lean_inc_ref(v_signature_4283_);
v___y_4288_ = v___x_4331_;
v___y_4289_ = v_signature_4283_;
goto v___jp_4287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object* v_signature_4348_, lean_object* v_separationTk_4349_, lean_object* v_body_4350_, lean_object* v_sticky_4351_){
_start:
{
uint8_t v_sticky_boxed_4352_; lean_object* v_res_4353_; 
v_sticky_boxed_4352_ = lean_unbox(v_sticky_4351_);
v_res_4353_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_4348_, v_separationTk_4349_, v_body_4350_, v_sticky_boxed_4352_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object* v_signature_4354_, lean_object* v_matchAlts_4355_){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4356_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4354_);
v___x_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
v___x_4358_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4359_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4357_, v___x_4358_);
v___x_4360_ = lean_box(0);
v___x_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4361_, 0, v_matchAlts_4355_);
v___x_4362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set(v___x_4362_, 1, v___x_4361_);
lean_ctor_set(v___x_4362_, 2, v___x_4360_);
v___x_4363_ = lean_unsigned_to_nat(2u);
v___x_4364_ = lean_mk_empty_array_with_capacity(v___x_4363_);
v___x_4365_ = lean_array_push(v___x_4364_, v___x_4359_);
v___x_4366_ = lean_array_push(v___x_4365_, v___x_4362_);
v___x_4367_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4366_);
lean_dec_ref(v___x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object* v_signature_4368_, lean_object* v_whereTk_4369_, lean_object* v_body_4370_){
_start:
{
uint8_t v___x_4371_; 
v___x_4371_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4370_);
if (v___x_4371_ == 0)
{
uint8_t v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v_lhs_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4372_ = 1;
v___x_4373_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4368_);
v___x_4374_ = lean_unsigned_to_nat(2u);
v___x_4375_ = lean_mk_empty_array_with_capacity(v___x_4374_);
v___x_4376_ = lean_array_push(v___x_4375_, v___x_4373_);
v___x_4377_ = lean_array_push(v___x_4376_, v_whereTk_4369_);
v_lhs_4378_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4377_);
lean_dec_ref(v___x_4377_);
v___x_4379_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4380_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4378_, v___x_4379_, v_body_4370_, v___x_4372_);
v___x_4381_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4380_);
return v___x_4381_;
}
else
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_dec_ref(v_body_4370_);
v___x_4382_ = lean_unsigned_to_nat(2u);
v___x_4383_ = lean_mk_empty_array_with_capacity(v___x_4382_);
v___x_4384_ = lean_array_push(v___x_4383_, v_signature_4368_);
v___x_4385_ = lean_array_push(v___x_4384_, v_whereTk_4369_);
v___x_4386_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4385_);
lean_dec_ref(v___x_4385_);
return v___x_4386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object* v_lbs_4388_, lean_object* v_lhses_4389_, lean_object* v_subBinderGroups_4390_, lean_object* v_typeAscriptionTk_x3f_4391_, lean_object* v_type_x3f_4392_, lean_object* v_colonEqTk_x3f_4393_, lean_object* v_default_x3f_4394_, lean_object* v_rbs_4395_, uint8_t v_kind_4396_){
_start:
{
lean_object* v_lbs_4397_; lean_object* v___x_4398_; lean_object* v_binderSignature_4399_; uint8_t v___x_4400_; lean_object* v_simpleBinder_4401_; lean_object* v_rbs_4402_; lean_object* v___x_4403_; 
v_lbs_4397_ = l_Lean_Fmt_Layouts_atomic(v_lbs_4388_);
v___x_4398_ = ((lean_object*)(l_Lean_Fmt_Layouts_binder___closed__0));
v_binderSignature_4399_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lhses_4389_, v_subBinderGroups_4390_, v_typeAscriptionTk_x3f_4391_, v_type_x3f_4392_, v_kind_4396_, v___x_4398_);
v___x_4400_ = 0;
v_simpleBinder_4401_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_binderSignature_4399_, v_colonEqTk_x3f_4393_, v_default_x3f_4394_, v___x_4400_);
v_rbs_4402_ = l_Lean_Fmt_Layouts_atomic(v_rbs_4395_);
v___x_4403_ = l_Lean_Fmt_Layouts_parens(v_lbs_4397_, v_simpleBinder_4401_, v_rbs_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object* v_lbs_4404_, lean_object* v_lhses_4405_, lean_object* v_subBinderGroups_4406_, lean_object* v_typeAscriptionTk_x3f_4407_, lean_object* v_type_x3f_4408_, lean_object* v_colonEqTk_x3f_4409_, lean_object* v_default_x3f_4410_, lean_object* v_rbs_4411_, lean_object* v_kind_4412_){
_start:
{
uint8_t v_kind_boxed_4413_; lean_object* v_res_4414_; 
v_kind_boxed_4413_ = lean_unbox(v_kind_4412_);
v_res_4414_ = l_Lean_Fmt_Layouts_binder(v_lbs_4404_, v_lhses_4405_, v_subBinderGroups_4406_, v_typeAscriptionTk_x3f_4407_, v_type_x3f_4408_, v_colonEqTk_x3f_4409_, v_default_x3f_4410_, v_rbs_4411_, v_kind_boxed_4413_);
lean_dec_ref(v_rbs_4411_);
lean_dec_ref(v_lhses_4405_);
lean_dec_ref(v_lbs_4404_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object* v_keywordTk_4418_, lean_object* v_config_4419_, lean_object* v_decl_4420_, uint8_t v_format_4421_){
_start:
{
lean_object* v___f_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v_signature_4428_; lean_object* v___y_4430_; 
v___f_4422_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_4423_ = lean_unsigned_to_nat(2u);
v___x_4424_ = lean_mk_empty_array_with_capacity(v___x_4423_);
lean_inc_ref(v___x_4424_);
v___x_4425_ = lean_array_push(v___x_4424_, v_keywordTk_4418_);
v___x_4426_ = lean_array_push(v___x_4425_, v_config_4419_);
v___x_4427_ = ((lean_object*)(l_Lean_Fmt_Layouts_letDecl___closed__0));
v_signature_4428_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4426_, v___x_4427_);
if (v_format_4421_ == 0)
{
lean_object* v___x_4442_; 
v___x_4442_ = l_Lean_Fmt_TaggedDoc_space;
v___y_4430_ = v___x_4442_;
goto v___jp_4429_;
}
else
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4430_ = v___x_4443_;
goto v___jp_4429_;
}
v___jp_4429_:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4431_, 0, v_signature_4428_);
lean_inc_ref(v___y_4430_);
v___x_4432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___y_4430_);
lean_ctor_set(v___x_4432_, 1, v___f_4422_);
v___x_4433_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4431_, v___x_4432_);
v___x_4434_ = lean_box(0);
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v_decl_4420_);
v___x_4436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4434_);
lean_ctor_set(v___x_4436_, 1, v___x_4435_);
lean_ctor_set(v___x_4436_, 2, v___x_4434_);
v___x_4437_ = lean_array_push(v___x_4424_, v___x_4433_);
v___x_4438_ = lean_array_push(v___x_4437_, v___x_4436_);
v___x_4439_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4438_);
lean_dec_ref(v___x_4438_);
v___x_4440_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4439_);
v___x_4441_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4440_);
return v___x_4441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object* v_keywordTk_4444_, lean_object* v_config_4445_, lean_object* v_decl_4446_, lean_object* v_format_4447_){
_start:
{
uint8_t v_format_boxed_4448_; lean_object* v_res_4449_; 
v_format_boxed_4448_ = lean_unbox(v_format_4447_);
v_res_4449_ = l_Lean_Fmt_Layouts_letDecl(v_keywordTk_4444_, v_config_4445_, v_decl_4446_, v_format_boxed_4448_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t v_sz_4450_, size_t v_i_4451_, lean_object* v_bs_4452_){
_start:
{
uint8_t v___x_4453_; 
v___x_4453_ = lean_usize_dec_lt(v_i_4451_, v_sz_4450_);
if (v___x_4453_ == 0)
{
return v_bs_4452_;
}
else
{
lean_object* v_v_4454_; lean_object* v_quantifier_4455_; lean_object* v_binderGroups_4456_; lean_object* v_typeAscriptionTk_x3f_4457_; lean_object* v_type_x3f_4458_; lean_object* v_separationTk_4459_; lean_object* v___x_4460_; lean_object* v_bs_x27_4461_; lean_object* v___x_4462_; lean_object* v_signature_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; uint8_t v___x_4469_; lean_object* v___x_4470_; size_t v___x_4471_; size_t v___x_4472_; lean_object* v___x_4473_; 
v_v_4454_ = lean_array_uget_borrowed(v_bs_4452_, v_i_4451_);
v_quantifier_4455_ = lean_ctor_get(v_v_4454_, 0);
lean_inc_ref(v_quantifier_4455_);
v_binderGroups_4456_ = lean_ctor_get(v_v_4454_, 1);
lean_inc_ref(v_binderGroups_4456_);
v_typeAscriptionTk_x3f_4457_ = lean_ctor_get(v_v_4454_, 2);
lean_inc_ref(v_typeAscriptionTk_x3f_4457_);
v_type_x3f_4458_ = lean_ctor_get(v_v_4454_, 3);
lean_inc_ref(v_type_x3f_4458_);
v_separationTk_4459_ = lean_ctor_get(v_v_4454_, 4);
lean_inc_ref(v_separationTk_4459_);
v___x_4460_ = lean_unsigned_to_nat(0u);
v_bs_x27_4461_ = lean_array_uset(v_bs_4452_, v_i_4451_, v___x_4460_);
v___x_4462_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v_signature_4463_ = l_Lean_Fmt_Layouts_localSignature(v___x_4462_, v_binderGroups_4456_, v_typeAscriptionTk_x3f_4457_, v_type_x3f_4458_);
v___x_4464_ = lean_unsigned_to_nat(2u);
v___x_4465_ = lean_mk_empty_array_with_capacity(v___x_4464_);
v___x_4466_ = lean_array_push(v___x_4465_, v_signature_4463_);
v___x_4467_ = lean_array_push(v___x_4466_, v_separationTk_4459_);
v___x_4468_ = l_Lean_Fmt_Layouts_atomic(v___x_4467_);
lean_dec_ref(v___x_4467_);
v___x_4469_ = 2;
v___x_4470_ = l_Lean_Fmt_Layouts_prefixOperator(v_quantifier_4455_, v___x_4468_, v___x_4469_);
v___x_4471_ = ((size_t)1ULL);
v___x_4472_ = lean_usize_add(v_i_4451_, v___x_4471_);
v___x_4473_ = lean_array_uset(v_bs_x27_4461_, v_i_4451_, v___x_4470_);
v_i_4451_ = v___x_4472_;
v_bs_4452_ = v___x_4473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object* v_sz_4475_, lean_object* v_i_4476_, lean_object* v_bs_4477_){
_start:
{
size_t v_sz_boxed_4478_; size_t v_i_boxed_4479_; lean_object* v_res_4480_; 
v_sz_boxed_4478_ = lean_unbox_usize(v_sz_4475_);
lean_dec(v_sz_4475_);
v_i_boxed_4479_ = lean_unbox_usize(v_i_4476_);
lean_dec(v_i_4476_);
v_res_4480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_boxed_4478_, v_i_boxed_4479_, v_bs_4477_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t v_sz_4481_, size_t v_i_4482_, lean_object* v_bs_4483_){
_start:
{
uint8_t v___x_4484_; 
v___x_4484_ = lean_usize_dec_lt(v_i_4482_, v_sz_4481_);
if (v___x_4484_ == 0)
{
return v_bs_4483_;
}
else
{
lean_object* v_v_4485_; lean_object* v___x_4486_; lean_object* v_bs_x27_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; size_t v___x_4490_; size_t v___x_4491_; lean_object* v___x_4492_; 
v_v_4485_ = lean_array_uget(v_bs_4483_, v_i_4482_);
v___x_4486_ = lean_unsigned_to_nat(0u);
v_bs_x27_4487_ = lean_array_uset(v_bs_4483_, v_i_4482_, v___x_4486_);
v___x_4488_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4485_);
v___x_4489_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
lean_ctor_set_uint8(v___x_4489_, sizeof(void*)*1, v___x_4484_);
v___x_4490_ = ((size_t)1ULL);
v___x_4491_ = lean_usize_add(v_i_4482_, v___x_4490_);
v___x_4492_ = lean_array_uset(v_bs_x27_4487_, v_i_4482_, v___x_4489_);
v_i_4482_ = v___x_4491_;
v_bs_4483_ = v___x_4492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object* v_sz_4494_, lean_object* v_i_4495_, lean_object* v_bs_4496_){
_start:
{
size_t v_sz_boxed_4497_; size_t v_i_boxed_4498_; lean_object* v_res_4499_; 
v_sz_boxed_4497_ = lean_unbox_usize(v_sz_4494_);
lean_dec(v_sz_4494_);
v_i_boxed_4498_ = lean_unbox_usize(v_i_4495_);
lean_dec(v_i_4495_);
v_res_4499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_boxed_4497_, v_i_boxed_4498_, v_bs_4496_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object* v_quantifierHeads_4500_, lean_object* v_body_4501_){
_start:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; uint8_t v___x_4504_; 
v___x_4502_ = lean_array_get_size(v_quantifierHeads_4500_);
v___x_4503_ = lean_unsigned_to_nat(0u);
v___x_4504_ = lean_nat_dec_eq(v___x_4502_, v___x_4503_);
if (v___x_4504_ == 0)
{
size_t v_sz_4505_; size_t v___x_4506_; lean_object* v_quantifierHeads_4507_; size_t v_sz_4508_; lean_object* v_quantifierHeads_4509_; lean_object* v___x_4510_; lean_object* v_components_4511_; lean_object* v___x_4512_; lean_object* v_quantifiers_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; 
v_sz_4505_ = lean_array_size(v_quantifierHeads_4500_);
v___x_4506_ = ((size_t)0ULL);
v_quantifierHeads_4507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_4505_, v___x_4506_, v_quantifierHeads_4500_);
v_sz_4508_ = lean_array_size(v_quantifierHeads_4507_);
v_quantifierHeads_4509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_4508_, v___x_4506_, v_quantifierHeads_4507_);
v___x_4510_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4510_, 0, v_body_4501_);
lean_ctor_set_uint8(v___x_4510_, sizeof(void*)*1, v___x_4504_);
v_components_4511_ = lean_array_push(v_quantifierHeads_4509_, v___x_4510_);
v___x_4512_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_quantifiers_4513_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(v_components_4511_, v___x_4512_);
v___x_4514_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_quantifiers_4513_);
v___x_4515_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4514_);
return v___x_4515_;
}
else
{
lean_dec_ref(v_quantifierHeads_4500_);
return v_body_4501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object* v_lbTk_4519_, lean_object* v_lhs_4520_, lean_object* v_sepTk_4521_, lean_object* v_rhs_4522_, lean_object* v_rbTk_4523_, lean_object* v_format_4524_){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v_body_4532_; lean_object* v___x_4533_; 
v___x_4525_ = lean_unsigned_to_nat(3u);
v___x_4526_ = lean_mk_empty_array_with_capacity(v___x_4525_);
v___x_4527_ = lean_array_push(v___x_4526_, v_lhs_4520_);
v___x_4528_ = lean_array_push(v___x_4527_, v_sepTk_4521_);
v___x_4529_ = lean_array_push(v___x_4528_, v_rhs_4522_);
v___x_4530_ = ((lean_object*)(l_Lean_Fmt_Layouts_subtype___closed__0));
v___x_4531_ = l_Lean_Fmt_Layouts_infixOperator(v___x_4529_, v___x_4530_);
v_body_4532_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4531_);
v___x_4533_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_4519_, v_body_4532_, v_rbTk_4523_, v_format_4524_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object* v_tk_4534_, lean_object* v_block_4535_, uint8_t v_allowFlattening_4536_){
_start:
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
v___x_4537_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4538_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tk_4534_, v___x_4537_, v_block_4535_, v_allowFlattening_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object* v_tk_4539_, lean_object* v_block_4540_, lean_object* v_allowFlattening_4541_){
_start:
{
uint8_t v_allowFlattening_boxed_4542_; lean_object* v_res_4543_; 
v_allowFlattening_boxed_4542_ = lean_unbox(v_allowFlattening_4541_);
v_res_4543_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_tk_4539_, v_block_4540_, v_allowFlattening_boxed_4542_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t v_allowFlattening_4544_, size_t v_sz_4545_, size_t v_i_4546_, lean_object* v_bs_4547_){
_start:
{
uint8_t v___x_4548_; 
v___x_4548_ = lean_usize_dec_lt(v_i_4546_, v_sz_4545_);
if (v___x_4548_ == 0)
{
return v_bs_4547_;
}
else
{
lean_object* v_v_4549_; lean_object* v_elseTk_4550_; lean_object* v_ifTk_4551_; lean_object* v_cond_4552_; lean_object* v_thenTk_4553_; lean_object* v_thenBlock_4554_; lean_object* v___x_4555_; lean_object* v_bs_x27_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v_tk_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; uint8_t v___x_4564_; lean_object* v___x_4565_; lean_object* v_head_4566_; lean_object* v_then_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v_trailingThen_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v_leadingThen_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; size_t v___x_4587_; size_t v___x_4588_; lean_object* v___x_4589_; 
v_v_4549_ = lean_array_uget_borrowed(v_bs_4547_, v_i_4546_);
v_elseTk_4550_ = lean_ctor_get(v_v_4549_, 0);
lean_inc_ref(v_elseTk_4550_);
v_ifTk_4551_ = lean_ctor_get(v_v_4549_, 1);
lean_inc_ref(v_ifTk_4551_);
v_cond_4552_ = lean_ctor_get(v_v_4549_, 2);
lean_inc_ref(v_cond_4552_);
v_thenTk_4553_ = lean_ctor_get(v_v_4549_, 3);
lean_inc_ref(v_thenTk_4553_);
v_thenBlock_4554_ = lean_ctor_get(v_v_4549_, 4);
lean_inc_ref(v_thenBlock_4554_);
v___x_4555_ = lean_unsigned_to_nat(0u);
v_bs_x27_4556_ = lean_array_uset(v_bs_4547_, v_i_4546_, v___x_4555_);
v___x_4557_ = lean_unsigned_to_nat(2u);
v___x_4558_ = lean_mk_empty_array_with_capacity(v___x_4557_);
lean_inc_ref_n(v___x_4558_, 4);
v___x_4559_ = lean_array_push(v___x_4558_, v_elseTk_4550_);
v___x_4560_ = lean_array_push(v___x_4559_, v_ifTk_4551_);
v_tk_4561_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4560_);
lean_dec_ref(v___x_4560_);
v___x_4562_ = lean_array_push(v___x_4558_, v_tk_4561_);
v___x_4563_ = lean_array_push(v___x_4562_, v_cond_4552_);
v___x_4564_ = 0;
v___x_4565_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4565_, 0, v___x_4548_);
lean_ctor_set_uint8(v___x_4565_, 1, v___x_4564_);
lean_ctor_set_uint8(v___x_4565_, 2, v___x_4564_);
lean_ctor_set_uint8(v___x_4565_, 3, v___x_4564_);
v_head_4566_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4563_, v___x_4565_);
v_then_4567_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_thenTk_4553_, v_thenBlock_4554_, v_allowFlattening_4544_);
lean_inc_ref(v_head_4566_);
v___x_4568_ = l_Lean_Fmt_TaggedDoc_flattened(v_head_4566_);
v___x_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4568_);
v___x_4570_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4571_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4569_, v___x_4570_);
v___x_4572_ = lean_box(0);
v___x_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4573_, 0, v_then_4567_);
v___x_4574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4572_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
lean_ctor_set(v___x_4574_, 2, v___x_4572_);
v___x_4575_ = lean_array_push(v___x_4558_, v___x_4571_);
lean_inc_ref(v___x_4574_);
v___x_4576_ = lean_array_push(v___x_4575_, v___x_4574_);
v_trailingThen_4577_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4576_);
lean_dec_ref(v___x_4576_);
v___x_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4578_, 0, v_head_4566_);
v___x_4579_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0);
v___x_4580_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4578_, v___x_4579_);
v___x_4581_ = lean_array_push(v___x_4558_, v___x_4580_);
v___x_4582_ = lean_array_push(v___x_4581_, v___x_4574_);
v_leadingThen_4583_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4582_);
lean_dec_ref(v___x_4582_);
v___x_4584_ = lean_array_push(v___x_4558_, v_trailingThen_4577_);
v___x_4585_ = lean_array_push(v___x_4584_, v_leadingThen_4583_);
v___x_4586_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_4585_);
v___x_4587_ = ((size_t)1ULL);
v___x_4588_ = lean_usize_add(v_i_4546_, v___x_4587_);
v___x_4589_ = lean_array_uset(v_bs_x27_4556_, v_i_4546_, v___x_4586_);
v_i_4546_ = v___x_4588_;
v_bs_4547_ = v___x_4589_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object* v_allowFlattening_4591_, lean_object* v_sz_4592_, lean_object* v_i_4593_, lean_object* v_bs_4594_){
_start:
{
uint8_t v_allowFlattening_boxed_4595_; size_t v_sz_boxed_4596_; size_t v_i_boxed_4597_; lean_object* v_res_4598_; 
v_allowFlattening_boxed_4595_ = lean_unbox(v_allowFlattening_4591_);
v_sz_boxed_4596_ = lean_unbox_usize(v_sz_4592_);
lean_dec(v_sz_4592_);
v_i_boxed_4597_ = lean_unbox_usize(v_i_4593_);
lean_dec(v_i_4593_);
v_res_4598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_boxed_4595_, v_sz_boxed_4596_, v_i_boxed_4597_, v_bs_4594_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object* v_elseIfs_4599_, lean_object* v_elseTk_4600_, lean_object* v_elseBlock_4601_, uint8_t v_allowFlattening_4602_){
_start:
{
size_t v_sz_4603_; size_t v___x_4604_; lean_object* v_elseIfs_4605_; lean_object* v_else_4606_; lean_object* v_blocks_4607_; size_t v_sz_4608_; lean_object* v_blocks_4609_; lean_object* v_conditional_4610_; lean_object* v___x_4611_; 
v_sz_4603_ = lean_array_size(v_elseIfs_4599_);
v___x_4604_ = ((size_t)0ULL);
v_elseIfs_4605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_4602_, v_sz_4603_, v___x_4604_, v_elseIfs_4599_);
v_else_4606_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_elseTk_4600_, v_elseBlock_4601_, v_allowFlattening_4602_);
v_blocks_4607_ = lean_array_push(v_elseIfs_4605_, v_else_4606_);
v_sz_4608_ = lean_array_size(v_blocks_4607_);
v_blocks_4609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_4608_, v___x_4604_, v_blocks_4607_);
v_conditional_4610_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_4609_);
lean_dec_ref(v_blocks_4609_);
v___x_4611_ = l_Lean_Fmt_TaggedDoc_aligned(v_conditional_4610_);
return v___x_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object* v_elseIfs_4612_, lean_object* v_elseTk_4613_, lean_object* v_elseBlock_4614_, lean_object* v_allowFlattening_4615_){
_start:
{
uint8_t v_allowFlattening_boxed_4616_; lean_object* v_res_4617_; 
v_allowFlattening_boxed_4616_ = lean_unbox(v_allowFlattening_4615_);
v_res_4617_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4612_, v_elseTk_4613_, v_elseBlock_4614_, v_allowFlattening_boxed_4616_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object* v_as_4618_, size_t v_i_4619_, size_t v_stop_4620_, lean_object* v_b_4621_){
_start:
{
lean_object* v___y_4623_; uint8_t v___x_4627_; 
v___x_4627_ = lean_usize_dec_eq(v_i_4619_, v_stop_4620_);
if (v___x_4627_ == 0)
{
lean_object* v___x_4628_; uint8_t v___y_4630_; lean_object* v_elseTk_4641_; lean_object* v_ifTk_4642_; uint8_t v___x_4643_; 
v___x_4628_ = lean_array_uget_borrowed(v_as_4618_, v_i_4619_);
v_elseTk_4641_ = lean_ctor_get(v___x_4628_, 0);
v_ifTk_4642_ = lean_ctor_get(v___x_4628_, 1);
v___x_4643_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_elseTk_4641_);
if (v___x_4643_ == 0)
{
v___y_4630_ = v___x_4643_;
goto v___jp_4629_;
}
else
{
uint8_t v___x_4644_; 
v___x_4644_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_ifTk_4642_);
v___y_4630_ = v___x_4644_;
goto v___jp_4629_;
}
v___jp_4629_:
{
if (v___y_4630_ == 0)
{
lean_object* v___x_4631_; 
lean_inc(v___x_4628_);
v___x_4631_ = lean_array_push(v_b_4621_, v___x_4628_);
v___y_4623_ = v___x_4631_;
goto v___jp_4622_;
}
else
{
lean_object* v_cond_4632_; lean_object* v_thenTk_4633_; lean_object* v_thenBlock_4634_; uint8_t v___x_4635_; 
v_cond_4632_ = lean_ctor_get(v___x_4628_, 2);
v_thenTk_4633_ = lean_ctor_get(v___x_4628_, 3);
v_thenBlock_4634_ = lean_ctor_get(v___x_4628_, 4);
v___x_4635_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_cond_4632_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; 
lean_inc(v___x_4628_);
v___x_4636_ = lean_array_push(v_b_4621_, v___x_4628_);
v___y_4623_ = v___x_4636_;
goto v___jp_4622_;
}
else
{
uint8_t v___x_4637_; 
v___x_4637_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenTk_4633_);
if (v___x_4637_ == 0)
{
lean_object* v___x_4638_; 
lean_inc(v___x_4628_);
v___x_4638_ = lean_array_push(v_b_4621_, v___x_4628_);
v___y_4623_ = v___x_4638_;
goto v___jp_4622_;
}
else
{
uint8_t v___x_4639_; 
v___x_4639_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenBlock_4634_);
if (v___x_4639_ == 0)
{
lean_object* v___x_4640_; 
lean_inc(v___x_4628_);
v___x_4640_ = lean_array_push(v_b_4621_, v___x_4628_);
v___y_4623_ = v___x_4640_;
goto v___jp_4622_;
}
else
{
v___y_4623_ = v_b_4621_;
goto v___jp_4622_;
}
}
}
}
}
}
else
{
return v_b_4621_;
}
v___jp_4622_:
{
size_t v___x_4624_; size_t v___x_4625_; 
v___x_4624_ = ((size_t)1ULL);
v___x_4625_ = lean_usize_add(v_i_4619_, v___x_4624_);
v_i_4619_ = v___x_4625_;
v_b_4621_ = v___y_4623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object* v_as_4645_, lean_object* v_i_4646_, lean_object* v_stop_4647_, lean_object* v_b_4648_){
_start:
{
size_t v_i_boxed_4649_; size_t v_stop_boxed_4650_; lean_object* v_res_4651_; 
v_i_boxed_4649_ = lean_unbox_usize(v_i_4646_);
lean_dec(v_i_4646_);
v_stop_boxed_4650_ = lean_unbox_usize(v_stop_4647_);
lean_dec(v_stop_4647_);
v_res_4651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_as_4645_, v_i_boxed_4649_, v_stop_boxed_4650_, v_b_4648_);
lean_dec_ref(v_as_4645_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object* v_ifTk_4654_, lean_object* v_cond_4655_, lean_object* v_thenTk_4656_, lean_object* v_thenBlock_4657_, lean_object* v_elseIfs_4658_, lean_object* v_elseTk_4659_, lean_object* v_elseBlock_4660_, uint8_t v_allowFlattening_4661_){
_start:
{
lean_object* v___y_4663_; uint8_t v___y_4664_; lean_object* v___y_4683_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; uint8_t v___x_4690_; 
v___x_4687_ = lean_unsigned_to_nat(0u);
v___x_4688_ = lean_array_get_size(v_elseIfs_4658_);
v___x_4689_ = ((lean_object*)(l_Lean_Fmt_Layouts_conditional___closed__0));
v___x_4690_ = lean_nat_dec_lt(v___x_4687_, v___x_4688_);
if (v___x_4690_ == 0)
{
v___y_4683_ = v___x_4689_;
goto v___jp_4682_;
}
else
{
uint8_t v___x_4691_; 
v___x_4691_ = lean_nat_dec_le(v___x_4688_, v___x_4688_);
if (v___x_4691_ == 0)
{
if (v___x_4690_ == 0)
{
v___y_4683_ = v___x_4689_;
goto v___jp_4682_;
}
else
{
size_t v___x_4692_; size_t v___x_4693_; lean_object* v___x_4694_; 
v___x_4692_ = ((size_t)0ULL);
v___x_4693_ = lean_usize_of_nat(v___x_4688_);
v___x_4694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_4658_, v___x_4692_, v___x_4693_, v___x_4689_);
v___y_4683_ = v___x_4694_;
goto v___jp_4682_;
}
}
else
{
size_t v___x_4695_; size_t v___x_4696_; lean_object* v___x_4697_; 
v___x_4695_ = ((size_t)0ULL);
v___x_4696_ = lean_usize_of_nat(v___x_4688_);
v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_4658_, v___x_4695_, v___x_4696_, v___x_4689_);
v___y_4683_ = v___x_4697_;
goto v___jp_4682_;
}
}
v___jp_4662_:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v_elseIfs_4670_; 
v___x_4665_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_4666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
lean_ctor_set(v___x_4666_, 1, v_ifTk_4654_);
lean_ctor_set(v___x_4666_, 2, v_cond_4655_);
lean_ctor_set(v___x_4666_, 3, v_thenTk_4656_);
lean_ctor_set(v___x_4666_, 4, v_thenBlock_4657_);
v___x_4667_ = lean_unsigned_to_nat(1u);
v___x_4668_ = lean_mk_empty_array_with_capacity(v___x_4667_);
v___x_4669_ = lean_array_push(v___x_4668_, v___x_4666_);
v_elseIfs_4670_ = l_Array_append___redArg(v___x_4669_, v___y_4663_);
lean_dec_ref(v___y_4663_);
if (v___y_4664_ == 0)
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
v___x_4671_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4670_, v_elseTk_4659_, v_elseBlock_4660_, v___y_4664_);
v___x_4672_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_4671_);
return v___x_4672_;
}
else
{
lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
lean_inc_ref(v_elseBlock_4660_);
lean_inc_ref(v_elseTk_4659_);
lean_inc_ref(v_elseIfs_4670_);
v___x_4673_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4670_, v_elseTk_4659_, v_elseBlock_4660_, v___y_4664_);
v___x_4674_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_4673_);
v___x_4675_ = 0;
v___x_4676_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_4670_, v_elseTk_4659_, v_elseBlock_4660_, v___x_4675_);
v___x_4677_ = lean_unsigned_to_nat(2u);
v___x_4678_ = lean_mk_empty_array_with_capacity(v___x_4677_);
v___x_4679_ = lean_array_push(v___x_4678_, v___x_4674_);
v___x_4680_ = lean_array_push(v___x_4679_, v___x_4676_);
v___x_4681_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_4680_);
return v___x_4681_;
}
}
v___jp_4682_:
{
if (v_allowFlattening_4661_ == 0)
{
v___y_4663_ = v___y_4683_;
v___y_4664_ = v_allowFlattening_4661_;
goto v___jp_4662_;
}
else
{
lean_object* v___x_4684_; lean_object* v___x_4685_; uint8_t v___x_4686_; 
v___x_4684_ = lean_array_get_size(v___y_4683_);
v___x_4685_ = lean_unsigned_to_nat(0u);
v___x_4686_ = lean_nat_dec_eq(v___x_4684_, v___x_4685_);
v___y_4663_ = v___y_4683_;
v___y_4664_ = v___x_4686_;
goto v___jp_4662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object* v_ifTk_4698_, lean_object* v_cond_4699_, lean_object* v_thenTk_4700_, lean_object* v_thenBlock_4701_, lean_object* v_elseIfs_4702_, lean_object* v_elseTk_4703_, lean_object* v_elseBlock_4704_, lean_object* v_allowFlattening_4705_){
_start:
{
uint8_t v_allowFlattening_boxed_4706_; lean_object* v_res_4707_; 
v_allowFlattening_boxed_4706_ = lean_unbox(v_allowFlattening_4705_);
v_res_4707_ = l_Lean_Fmt_Layouts_conditional(v_ifTk_4698_, v_cond_4699_, v_thenTk_4700_, v_thenBlock_4701_, v_elseIfs_4702_, v_elseTk_4703_, v_elseBlock_4704_, v_allowFlattening_boxed_4706_);
lean_dec_ref(v_elseIfs_4702_);
return v_res_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object* v_prefix_4708_, lean_object* v_str_4709_){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; uint8_t v___x_4715_; lean_object* v___x_4716_; 
v___x_4710_ = lean_unsigned_to_nat(2u);
v___x_4711_ = lean_mk_empty_array_with_capacity(v___x_4710_);
v___x_4712_ = lean_array_push(v___x_4711_, v_prefix_4708_);
v___x_4713_ = lean_array_push(v___x_4712_, v_str_4709_);
v___x_4714_ = l_Lean_Fmt_Layouts_atomic(v___x_4713_);
lean_dec_ref(v___x_4713_);
v___x_4715_ = 0;
v___x_4716_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_4714_, v___x_4715_);
return v___x_4716_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default = _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default();
lean_mark_persistent(l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default);
l_Lean_Fmt_Layouts_Types_instInhabitedBlock = _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock();
lean_mark_persistent(l_Lean_Fmt_Layouts_Types_instInhabitedBlock);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Primitives(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_FmtM_Layouts(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Primitives(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_FmtM_Layouts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_FmtM_Layouts(builtin);
}
#ifdef __cplusplus
}
#endif

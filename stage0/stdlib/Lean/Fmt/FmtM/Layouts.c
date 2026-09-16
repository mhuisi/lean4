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
extern lean_object* l_Lean_Fmt_instInhabitedTaggedDoc_default;
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
extern lean_object* l_Lean_Fmt_TaggedDoc_softSpace;
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_untagged(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Fmt_TaggedDoc_sticky(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_guarded(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fill(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isRawFallback(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isAtomic(lean_object*);
uint8_t l_Lean_Fmt_TaggedDoc_isSelfDelimited(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Fmt_Layouts_lines___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_lines___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_lines___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines___boxed(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Fmt_Layouts_sepFill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_sepFill___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_sepFill___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Fmt_Layouts_bracketed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Layouts_bracketed___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_bracketed___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Layouts_parens___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_parens___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_parens___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_sepFill___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_Layouts_sepFill___closed__0_value)}};
static const lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1_value;
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
static const lean_ctor_object l_Lean_Fmt_Layouts_pipeOperator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_localSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_localSignature___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Fmt_Layouts_localSignature___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_localSignature___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Layouts_localSignature___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Fmt_Layouts_localSignature___closed__1 = (const lean_object*)&l_Lean_Fmt_Layouts_localSignature___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_globalSignature___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_globalSignature___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_globalSignature___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Layouts_binder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Layouts_fill___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Layouts_binder___closed__0 = (const lean_object*)&l_Lean_Fmt_Layouts_binder___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorIdx(v_x_8_);
lean_dec(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
if (lean_obj_tag(v_t_10_) == 3)
{
uint8_t v_allowFlattening_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_allowFlattening_12_ = lean_ctor_get_uint8(v_t_10_, 0);
v___x_13_ = lean_box(v_allowFlattening_12_);
v___x_14_ = lean_apply_1(v_k_11_, v___x_13_);
return v___x_14_;
}
else
{
return v_k_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg___boxed(lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_15_, v_k_16_);
lean_dec(v_t_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_t_26_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(lean_object* v_t_30_, lean_object* v_join_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_30_, v_join_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg___boxed(lean_object* v_t_33_, lean_object* v_join_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___redArg(v_t_33_, v_join_34_);
lean_dec(v_t_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_join_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_37_, v_join_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim___boxed(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_join_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_join_elim(v_motive_41_, v_t_42_, v_h_43_, v_join_44_);
lean_dec(v_t_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(lean_object* v_t_46_, lean_object* v_joinUsingSpace_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_46_, v_joinUsingSpace_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg___boxed(lean_object* v_t_49_, lean_object* v_joinUsingSpace_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___redArg(v_t_49_, v_joinUsingSpace_50_);
lean_dec(v_t_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_joinUsingSpace_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_53_, v_joinUsingSpace_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim___boxed(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_joinUsingSpace_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSpace_elim(v_motive_57_, v_t_58_, v_h_59_, v_joinUsingSpace_60_);
lean_dec(v_t_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(lean_object* v_t_62_, lean_object* v_joinUsingSoftSpace_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_62_, v_joinUsingSoftSpace_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg___boxed(lean_object* v_t_65_, lean_object* v_joinUsingSoftSpace_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___redArg(v_t_65_, v_joinUsingSoftSpace_66_);
lean_dec(v_t_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_joinUsingSoftSpace_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_69_, v_joinUsingSoftSpace_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim___boxed(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_joinUsingSoftSpace_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingSoftSpace_elim(v_motive_73_, v_t_74_, v_h_75_, v_joinUsingSoftSpace_76_);
lean_dec(v_t_74_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_78_, lean_object* v_joinUsingNl_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_78_, v_joinUsingNl_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg___boxed(lean_object* v_t_81_, lean_object* v_joinUsingNl_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___redArg(v_t_81_, v_joinUsingNl_82_);
lean_dec(v_t_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_joinUsingNl_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_85_, v_joinUsingNl_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim___boxed(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_joinUsingNl_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingNl_elim(v_motive_89_, v_t_90_, v_h_91_, v_joinUsingNl_92_);
lean_dec(v_t_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(lean_object* v_t_94_, lean_object* v_joinUsingBreak_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_94_, v_joinUsingBreak_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg___boxed(lean_object* v_t_97_, lean_object* v_joinUsingBreak_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___redArg(v_t_97_, v_joinUsingBreak_98_);
lean_dec(v_t_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(lean_object* v_motive_100_, lean_object* v_t_101_, lean_object* v_h_102_, lean_object* v_joinUsingBreak_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_101_, v_joinUsingBreak_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim___boxed(lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_joinUsingBreak_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_joinUsingBreak_elim(v_motive_105_, v_t_106_, v_h_107_, v_joinUsingBreak_108_);
lean_dec(v_t_106_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(lean_object* v_t_110_, lean_object* v_fill_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_110_, v_fill_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg___boxed(lean_object* v_t_113_, lean_object* v_fill_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___redArg(v_t_113_, v_fill_114_);
lean_dec(v_t_113_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(lean_object* v_motive_116_, lean_object* v_t_117_, lean_object* v_h_118_, lean_object* v_fill_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_ctorElim___redArg(v_t_117_, v_fill_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim___boxed(lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_fill_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Fmt_Layouts_Types_ArrayFormat_fill_elim(v_motive_121_, v_t_122_, v_h_123_, v_fill_124_);
lean_dec(v_t_122_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(lean_object* v___y_126_){
_start:
{
lean_inc_ref(v___y_126_);
return v___y_126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0___boxed(lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___lam__0(v___y_127_);
lean_dec_ref(v___y_127_);
return v_res_128_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1(void){
_start:
{
lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___f_130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_131_ = l_Lean_Fmt_TaggedDoc_space;
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___f_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(size_t v_sz_133_, size_t v_i_134_, lean_object* v_bs_135_){
_start:
{
uint8_t v___x_136_; 
v___x_136_ = lean_usize_dec_lt(v_i_134_, v_sz_133_);
if (v___x_136_ == 0)
{
return v_bs_135_;
}
else
{
lean_object* v_v_137_; lean_object* v___x_138_; lean_object* v_bs_x27_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; size_t v___x_143_; size_t v___x_144_; lean_object* v___x_145_; 
v_v_137_ = lean_array_uget(v_bs_135_, v_i_134_);
v___x_138_ = lean_unsigned_to_nat(0u);
v_bs_x27_139_ = lean_array_uset(v_bs_135_, v_i_134_, v___x_138_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_v_137_);
v___x_141_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_142_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_140_, v___x_141_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_add(v_i_134_, v___x_143_);
v___x_145_ = lean_array_uset(v_bs_x27_139_, v_i_134_, v___x_142_);
v_i_134_ = v___x_144_;
v_bs_135_ = v___x_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___boxed(lean_object* v_sz_147_, lean_object* v_i_148_, lean_object* v_bs_149_){
_start:
{
size_t v_sz_boxed_150_; size_t v_i_boxed_151_; lean_object* v_res_152_; 
v_sz_boxed_150_ = lean_unbox_usize(v_sz_147_);
lean_dec(v_sz_147_);
v_i_boxed_151_ = lean_unbox_usize(v_i_148_);
lean_dec(v_i_148_);
v_res_152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_boxed_150_, v_i_boxed_151_, v_bs_149_);
return v_res_152_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0(void){
_start:
{
lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___f_153_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_154_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___f_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(size_t v_sz_156_, size_t v_i_157_, lean_object* v_bs_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_lt(v_i_157_, v_sz_156_);
if (v___x_159_ == 0)
{
return v_bs_158_;
}
else
{
lean_object* v_v_160_; lean_object* v___x_161_; lean_object* v_bs_x27_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_v_160_ = lean_array_uget(v_bs_158_, v_i_157_);
v___x_161_ = lean_unsigned_to_nat(0u);
v_bs_x27_162_ = lean_array_uset(v_bs_158_, v_i_157_, v___x_161_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_v_160_);
v___x_164_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___closed__0);
v___x_165_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_163_, v___x_164_);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_add(v_i_157_, v___x_166_);
v___x_168_ = lean_array_uset(v_bs_x27_162_, v_i_157_, v___x_165_);
v_i_157_ = v___x_167_;
v_bs_158_ = v___x_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0___boxed(lean_object* v_sz_170_, lean_object* v_i_171_, lean_object* v_bs_172_){
_start:
{
size_t v_sz_boxed_173_; size_t v_i_boxed_174_; lean_object* v_res_175_; 
v_sz_boxed_173_ = lean_unbox_usize(v_sz_170_);
lean_dec(v_sz_170_);
v_i_boxed_174_ = lean_unbox_usize(v_i_171_);
lean_dec(v_i_171_);
v_res_175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_boxed_173_, v_i_boxed_174_, v_bs_172_);
return v_res_175_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0(void){
_start:
{
lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___f_176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_177_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___f_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(size_t v_sz_179_, size_t v_i_180_, lean_object* v_bs_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_usize_dec_lt(v_i_180_, v_sz_179_);
if (v___x_182_ == 0)
{
return v_bs_181_;
}
else
{
lean_object* v_v_183_; lean_object* v___x_184_; lean_object* v_bs_x27_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; 
v_v_183_ = lean_array_uget(v_bs_181_, v_i_180_);
v___x_184_ = lean_unsigned_to_nat(0u);
v_bs_x27_185_ = lean_array_uset(v_bs_181_, v_i_180_, v___x_184_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_v_183_);
v___x_187_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___closed__0);
v___x_188_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_186_, v___x_187_);
v___x_189_ = ((size_t)1ULL);
v___x_190_ = lean_usize_add(v_i_180_, v___x_189_);
v___x_191_ = lean_array_uset(v_bs_x27_185_, v_i_180_, v___x_188_);
v_i_180_ = v___x_190_;
v_bs_181_ = v___x_191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3___boxed(lean_object* v_sz_193_, lean_object* v_i_194_, lean_object* v_bs_195_){
_start:
{
size_t v_sz_boxed_196_; size_t v_i_boxed_197_; lean_object* v_res_198_; 
v_sz_boxed_196_ = lean_unbox_usize(v_sz_193_);
lean_dec(v_sz_193_);
v_i_boxed_197_ = lean_unbox_usize(v_i_194_);
lean_dec(v_i_194_);
v_res_198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_boxed_196_, v_i_boxed_197_, v_bs_195_);
return v_res_198_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0(void){
_start:
{
lean_object* v___f_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___f_199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_200_ = l_Lean_Fmt_TaggedDoc_break;
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
lean_ctor_set(v___x_201_, 1, v___f_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(size_t v_sz_202_, size_t v_i_203_, lean_object* v_bs_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = lean_usize_dec_lt(v_i_203_, v_sz_202_);
if (v___x_205_ == 0)
{
return v_bs_204_;
}
else
{
lean_object* v_v_206_; lean_object* v___x_207_; lean_object* v_bs_x27_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v_v_206_ = lean_array_uget(v_bs_204_, v_i_203_);
v___x_207_ = lean_unsigned_to_nat(0u);
v_bs_x27_208_ = lean_array_uset(v_bs_204_, v_i_203_, v___x_207_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v_v_206_);
v___x_210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___closed__0);
v___x_211_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_209_, v___x_210_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_add(v_i_203_, v___x_212_);
v___x_214_ = lean_array_uset(v_bs_x27_208_, v_i_203_, v___x_211_);
v_i_203_ = v___x_213_;
v_bs_204_ = v___x_214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5___boxed(lean_object* v_sz_216_, lean_object* v_i_217_, lean_object* v_bs_218_){
_start:
{
size_t v_sz_boxed_219_; size_t v_i_boxed_220_; lean_object* v_res_221_; 
v_sz_boxed_219_ = lean_unbox_usize(v_sz_216_);
lean_dec(v_sz_216_);
v_i_boxed_220_ = lean_unbox_usize(v_i_217_);
lean_dec(v_i_217_);
v_res_221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(v_sz_boxed_219_, v_i_boxed_220_, v_bs_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(lean_object* v_as_222_, size_t v_i_223_, size_t v_stop_224_, lean_object* v_b_225_){
_start:
{
lean_object* v___y_227_; uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_eq(v_i_223_, v_stop_224_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_array_uget_borrowed(v_as_222_, v_i_223_);
v___x_233_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_inc(v___x_232_);
v___x_234_ = lean_array_push(v_b_225_, v___x_232_);
v___y_227_ = v___x_234_;
goto v___jp_226_;
}
else
{
v___y_227_ = v_b_225_;
goto v___jp_226_;
}
}
else
{
return v_b_225_;
}
v___jp_226_:
{
size_t v___x_228_; size_t v___x_229_; 
v___x_228_ = ((size_t)1ULL);
v___x_229_ = lean_usize_add(v_i_223_, v___x_228_);
v_i_223_ = v___x_229_;
v_b_225_ = v___y_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6___boxed(lean_object* v_as_235_, lean_object* v_i_236_, lean_object* v_stop_237_, lean_object* v_b_238_){
_start:
{
size_t v_i_boxed_239_; size_t v_stop_boxed_240_; lean_object* v_res_241_; 
v_i_boxed_239_ = lean_unbox_usize(v_i_236_);
lean_dec(v_i_236_);
v_stop_boxed_240_ = lean_unbox_usize(v_stop_237_);
lean_dec(v_stop_237_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_as_235_, v_i_boxed_239_, v_stop_boxed_240_, v_b_238_);
lean_dec_ref(v_as_235_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(lean_object* v_as_242_, size_t v_i_243_, size_t v_stop_244_, lean_object* v_b_245_){
_start:
{
lean_object* v___y_247_; uint8_t v___x_251_; 
v___x_251_ = lean_usize_dec_eq(v_i_243_, v_stop_244_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_array_uget_borrowed(v_as_242_, v_i_243_);
v___x_253_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_inc(v___x_252_);
v___x_254_ = lean_array_push(v_b_245_, v___x_252_);
v___y_247_ = v___x_254_;
goto v___jp_246_;
}
else
{
v___y_247_ = v_b_245_;
goto v___jp_246_;
}
}
else
{
return v_b_245_;
}
v___jp_246_:
{
size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; 
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_add(v_i_243_, v___x_248_);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_as_242_, v___x_249_, v_stop_244_, v___y_247_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6___boxed(lean_object* v_as_255_, lean_object* v_i_256_, lean_object* v_stop_257_, lean_object* v_b_258_){
_start:
{
size_t v_i_boxed_259_; size_t v_stop_boxed_260_; lean_object* v_res_261_; 
v_i_boxed_259_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_stop_boxed_260_ = lean_unbox_usize(v_stop_257_);
lean_dec(v_stop_257_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_as_255_, v_i_boxed_259_, v_stop_boxed_260_, v_b_258_);
lean_dec_ref(v_as_255_);
return v_res_261_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0(void){
_start:
{
lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___f_262_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_263_ = l_Lean_Fmt_TaggedDoc_softSpace;
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___f_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(size_t v_sz_265_, size_t v_i_266_, lean_object* v_bs_267_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = lean_usize_dec_lt(v_i_266_, v_sz_265_);
if (v___x_268_ == 0)
{
return v_bs_267_;
}
else
{
lean_object* v_v_269_; lean_object* v___x_270_; lean_object* v_bs_x27_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v_v_269_ = lean_array_uget(v_bs_267_, v_i_266_);
v___x_270_ = lean_unsigned_to_nat(0u);
v_bs_x27_271_ = lean_array_uset(v_bs_267_, v_i_266_, v___x_270_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v_v_269_);
v___x_273_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___closed__0);
v___x_274_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_272_, v___x_273_);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_266_, v___x_275_);
v___x_277_ = lean_array_uset(v_bs_x27_271_, v_i_266_, v___x_274_);
v_i_266_ = v___x_276_;
v_bs_267_ = v___x_277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2___boxed(lean_object* v_sz_279_, lean_object* v_i_280_, lean_object* v_bs_281_){
_start:
{
size_t v_sz_boxed_282_; size_t v_i_boxed_283_; lean_object* v_res_284_; 
v_sz_boxed_282_ = lean_unbox_usize(v_sz_279_);
lean_dec(v_sz_279_);
v_i_boxed_283_ = lean_unbox_usize(v_i_280_);
lean_dec(v_i_280_);
v_res_284_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_boxed_282_, v_i_boxed_283_, v_bs_281_);
return v_res_284_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0(void){
_start:
{
lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___f_285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_286_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___f_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(size_t v_sz_288_, size_t v_i_289_, lean_object* v_bs_290_){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = lean_usize_dec_lt(v_i_289_, v_sz_288_);
if (v___x_291_ == 0)
{
return v_bs_290_;
}
else
{
lean_object* v_v_292_; lean_object* v___x_293_; lean_object* v_bs_x27_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v___x_300_; 
v_v_292_ = lean_array_uget(v_bs_290_, v_i_289_);
v___x_293_ = lean_unsigned_to_nat(0u);
v_bs_x27_294_ = lean_array_uset(v_bs_290_, v_i_289_, v___x_293_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_v_292_);
v___x_296_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_297_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_295_, v___x_296_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_add(v_i_289_, v___x_298_);
v___x_300_ = lean_array_uset(v_bs_x27_294_, v_i_289_, v___x_297_);
v_i_289_ = v___x_299_;
v_bs_290_ = v___x_300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___boxed(lean_object* v_sz_302_, lean_object* v_i_303_, lean_object* v_bs_304_){
_start:
{
size_t v_sz_boxed_305_; size_t v_i_boxed_306_; lean_object* v_res_307_; 
v_sz_boxed_305_ = lean_unbox_usize(v_sz_302_);
lean_dec(v_sz_302_);
v_i_boxed_306_ = lean_unbox_usize(v_i_303_);
lean_dec(v_i_303_);
v_res_307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_boxed_305_, v_i_boxed_306_, v_bs_304_);
return v_res_307_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_array___closed__1(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_311_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array(lean_object* v_array_312_, lean_object* v_format_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___y_317_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_314_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_array_get_size(v_array_312_);
v___x_364_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_365_ = lean_nat_dec_lt(v___x_315_, v___x_363_);
if (v___x_365_ == 0)
{
v___y_317_ = v___x_364_;
goto v___jp_316_;
}
else
{
uint8_t v___x_366_; 
v___x_366_ = lean_nat_dec_le(v___x_363_, v___x_363_);
if (v___x_366_ == 0)
{
if (v___x_365_ == 0)
{
v___y_317_ = v___x_364_;
goto v___jp_316_;
}
else
{
size_t v___x_367_; size_t v___x_368_; lean_object* v___x_369_; 
v___x_367_ = ((size_t)0ULL);
v___x_368_ = lean_usize_of_nat(v___x_363_);
v___x_369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_array_312_, v___x_367_, v___x_368_, v___x_364_);
v___y_317_ = v___x_369_;
goto v___jp_316_;
}
}
else
{
size_t v___x_370_; size_t v___x_371_; lean_object* v___x_372_; 
v___x_370_ = ((size_t)0ULL);
v___x_371_ = lean_usize_of_nat(v___x_363_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_array_312_, v___x_370_, v___x_371_, v___x_364_);
v___y_317_ = v___x_372_;
goto v___jp_316_;
}
}
v___jp_316_:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_array_get_size(v___y_317_);
v___x_319_ = lean_nat_dec_eq(v___x_318_, v___x_315_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_dec_eq(v___x_318_, v___x_320_);
if (v___x_321_ == 0)
{
switch(lean_obj_tag(v_format_313_))
{
case 0:
{
size_t v_sz_322_; size_t v___x_323_; lean_object* v_terms_324_; lean_object* v___x_325_; 
v_sz_322_ = lean_array_size(v___y_317_);
v___x_323_ = ((size_t)0ULL);
v_terms_324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__0(v_sz_322_, v___x_323_, v___y_317_);
v___x_325_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_324_);
lean_dec_ref(v_terms_324_);
return v___x_325_;
}
case 1:
{
size_t v_sz_326_; size_t v___x_327_; lean_object* v_terms_328_; lean_object* v___x_329_; 
v_sz_326_ = lean_array_size(v___y_317_);
v___x_327_ = ((size_t)0ULL);
v_terms_328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1(v_sz_326_, v___x_327_, v___y_317_);
v___x_329_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_328_);
lean_dec_ref(v_terms_328_);
return v___x_329_;
}
case 2:
{
size_t v_sz_330_; size_t v___x_331_; lean_object* v_terms_332_; lean_object* v___x_333_; 
v_sz_330_ = lean_array_size(v___y_317_);
v___x_331_ = ((size_t)0ULL);
v_terms_332_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__2(v_sz_330_, v___x_331_, v___y_317_);
v___x_333_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_332_);
lean_dec_ref(v_terms_332_);
return v___x_333_;
}
case 3:
{
uint8_t v_allowFlattening_334_; 
v_allowFlattening_334_ = lean_ctor_get_uint8(v_format_313_, 0);
if (v_allowFlattening_334_ == 0)
{
size_t v_sz_335_; size_t v___x_336_; lean_object* v_terms_337_; lean_object* v___x_338_; 
v_sz_335_ = lean_array_size(v___y_317_);
v___x_336_ = ((size_t)0ULL);
v_terms_337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__3(v_sz_335_, v___x_336_, v___y_317_);
v___x_338_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_337_);
lean_dec_ref(v_terms_337_);
return v___x_338_;
}
else
{
size_t v_sz_339_; size_t v___x_340_; lean_object* v_terms_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_sz_339_ = lean_array_size(v___y_317_);
v___x_340_ = ((size_t)0ULL);
v_terms_341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_339_, v___x_340_, v___y_317_);
v___x_342_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_341_);
lean_dec_ref(v_terms_341_);
v___x_343_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_342_);
return v___x_343_;
}
}
case 4:
{
size_t v_sz_344_; size_t v___x_345_; lean_object* v_terms_346_; lean_object* v___x_347_; 
v_sz_344_ = lean_array_size(v___y_317_);
v___x_345_ = ((size_t)0ULL);
v_terms_346_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__5(v_sz_344_, v___x_345_, v___y_317_);
v___x_347_ = l_Lean_Fmt_TaggedDoc_combine(v_terms_346_);
lean_dec_ref(v_terms_346_);
return v___x_347_;
}
default: 
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_349_ = lean_nat_dec_lt(v___x_315_, v___x_318_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec_ref(v___y_317_);
v___x_350_ = lean_obj_once(&l_Lean_Fmt_Layouts_array___closed__1, &l_Lean_Fmt_Layouts_array___closed__1_once, _init_l_Lean_Fmt_Layouts_array___closed__1);
return v___x_350_;
}
else
{
uint8_t v___x_351_; 
v___x_351_ = lean_nat_dec_le(v___x_318_, v___x_318_);
if (v___x_351_ == 0)
{
if (v___x_349_ == 0)
{
lean_object* v___x_352_; 
lean_dec_ref(v___y_317_);
v___x_352_ = lean_obj_once(&l_Lean_Fmt_Layouts_array___closed__1, &l_Lean_Fmt_Layouts_array___closed__1_once, _init_l_Lean_Fmt_Layouts_array___closed__1);
return v___x_352_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_318_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v___y_317_, v___x_353_, v___x_354_, v___x_348_);
lean_dec_ref(v___y_317_);
v___x_356_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_355_);
return v___x_356_;
}
}
else
{
size_t v___x_357_; size_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_357_ = ((size_t)0ULL);
v___x_358_ = lean_usize_of_nat(v___x_318_);
v___x_359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v___y_317_, v___x_357_, v___x_358_, v___x_348_);
lean_dec_ref(v___y_317_);
v___x_360_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_359_);
return v___x_360_;
}
}
}
}
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_array_get(v___x_314_, v___y_317_, v___x_315_);
lean_dec_ref(v___y_317_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; 
lean_dec_ref(v___y_317_);
v___x_362_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_array___boxed(lean_object* v_array_373_, lean_object* v_format_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Fmt_Layouts_array(v_array_373_, v_format_374_);
lean_dec(v_format_374_);
lean_dec_ref(v_array_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines(lean_object* v_lines_378_){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_Fmt_Layouts_lines___closed__0));
v___x_380_ = l_Lean_Fmt_Layouts_array(v_lines_378_, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_lines___boxed(lean_object* v_lines_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Fmt_Layouts_lines(v_lines_381_);
lean_dec_ref(v_lines_381_);
return v_res_382_;
}
}
static uint8_t _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_384_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(size_t v_sz_385_, size_t v_i_386_, lean_object* v_bs_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_lt(v_i_386_, v_sz_385_);
if (v___x_388_ == 0)
{
return v_bs_387_;
}
else
{
lean_object* v___f_389_; lean_object* v_v_390_; lean_object* v___x_391_; lean_object* v_bs_x27_392_; lean_object* v___x_393_; lean_object* v___y_395_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___f_389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v_v_390_ = lean_array_uget(v_bs_387_, v_i_386_);
v___x_391_ = lean_unsigned_to_nat(0u);
v_bs_x27_392_ = lean_array_uset(v_bs_387_, v_i_386_, v___x_391_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_v_390_);
v___x_402_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_403_ = lean_uint8_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___closed__0);
if (v___x_403_ == 0)
{
if (v___x_403_ == 0)
{
lean_object* v_doc_404_; uint8_t v___x_405_; 
v_doc_404_ = lean_ctor_get(v___x_402_, 0);
v___x_405_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_404_);
if (v___x_405_ == 0)
{
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc_n(v_doc_404_, 2);
v___x_406_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_404_, v_doc_404_);
v___x_407_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_406_);
v___y_395_ = v___x_407_;
goto v___jp_394_;
}
else
{
lean_object* v___x_408_; 
lean_inc(v_doc_404_);
v___x_408_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_404_);
v___y_395_ = v___x_408_;
goto v___jp_394_;
}
}
else
{
lean_object* v___x_409_; 
lean_inc(v_doc_404_);
v___x_409_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_404_);
v___y_395_ = v___x_409_;
goto v___jp_394_;
}
}
else
{
v___y_395_ = v___x_402_;
goto v___jp_394_;
}
}
else
{
v___y_395_ = v___x_402_;
goto v___jp_394_;
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; 
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___y_395_);
lean_ctor_set(v___x_396_, 1, v___f_389_);
v___x_397_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_393_, v___x_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = lean_usize_add(v_i_386_, v___x_398_);
v___x_400_ = lean_array_uset(v_bs_x27_392_, v_i_386_, v___x_397_);
v_i_386_ = v___x_399_;
v_bs_387_ = v___x_400_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0___boxed(lean_object* v_sz_410_, lean_object* v_i_411_, lean_object* v_bs_412_){
_start:
{
size_t v_sz_boxed_413_; size_t v_i_boxed_414_; lean_object* v_res_415_; 
v_sz_boxed_413_ = lean_unbox_usize(v_sz_410_);
lean_dec(v_sz_410_);
v_i_boxed_414_ = lean_unbox_usize(v_i_411_);
lean_dec(v_i_411_);
v_res_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_boxed_413_, v_i_boxed_414_, v_bs_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedLines(lean_object* v_lines_416_){
_start:
{
size_t v_sz_417_; size_t v___x_418_; lean_object* v_lines_419_; lean_object* v___x_420_; 
v_sz_417_ = lean_array_size(v_lines_416_);
v___x_418_ = ((size_t)0ULL);
v_lines_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_spacedLines_spec__0(v_sz_417_, v___x_418_, v_lines_416_);
v___x_420_ = l_Lean_Fmt_TaggedDoc_combine(v_lines_419_);
lean_dec_ref(v_lines_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic(lean_object* v_terms_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_Fmt_Layouts_array(v_terms_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomic___boxed(lean_object* v_terms_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Fmt_Layouts_atomic(v_terms_424_);
lean_dec_ref(v_terms_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator(lean_object* v_terms_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___y_430_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_427_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_array_get_size(v_terms_426_);
v___x_438_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_439_ = lean_nat_dec_lt(v___x_428_, v___x_437_);
if (v___x_439_ == 0)
{
v___y_430_ = v___x_438_;
goto v___jp_429_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_le(v___x_437_, v___x_437_);
if (v___x_440_ == 0)
{
if (v___x_439_ == 0)
{
v___y_430_ = v___x_438_;
goto v___jp_429_;
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_437_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_terms_426_, v___x_441_, v___x_442_, v___x_438_);
v___y_430_ = v___x_443_;
goto v___jp_429_;
}
}
else
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((size_t)0ULL);
v___x_445_ = lean_usize_of_nat(v___x_437_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_terms_426_, v___x_444_, v___x_445_, v___x_438_);
v___y_430_ = v___x_446_;
goto v___jp_429_;
}
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_array_get_size(v___y_430_);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_dec_eq(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = l_Lean_Fmt_Layouts_atomic(v___y_430_);
lean_dec_ref(v___y_430_);
v___x_435_ = l_Lean_Fmt_TaggedDoc_nested(v___x_434_);
return v___x_435_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = lean_array_get(v___x_427_, v___y_430_, v___x_428_);
lean_dec_ref(v___y_430_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_atomicInfixOperator___boxed(lean_object* v_terms_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Fmt_Layouts_atomicInfixOperator(v_terms_447_);
lean_dec_ref(v_terms_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic(lean_object* v_terms_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_box(1);
v___x_451_ = l_Lean_Fmt_Layouts_array(v_terms_449_, v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_spacedAtomic___boxed(lean_object* v_terms_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Fmt_Layouts_spacedAtomic(v_terms_452_);
lean_dec_ref(v_terms_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic(lean_object* v_terms_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_box(2);
v___x_456_ = l_Lean_Fmt_Layouts_array(v_terms_454_, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_softSpacedAtomic___boxed(lean_object* v_terms_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Fmt_Layouts_softSpacedAtomic(v_terms_457_);
lean_dec_ref(v_terms_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill(lean_object* v_terms_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_box(5);
v___x_461_ = l_Lean_Fmt_Layouts_array(v_terms_459_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_fill___boxed(lean_object* v_terms_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Fmt_Layouts_fill(v_terms_462_);
lean_dec_ref(v_terms_462_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical(lean_object* v_terms_464_, uint8_t v_spacing_465_){
_start:
{
if (v_spacing_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_box(4);
v___x_467_ = l_Lean_Fmt_Layouts_array(v_terms_464_, v___x_466_);
return v___x_467_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_alloc_ctor(3, 0, 1);
lean_ctor_set_uint8(v___x_468_, 0, v_spacing_465_);
v___x_469_ = l_Lean_Fmt_Layouts_array(v_terms_464_, v___x_468_);
lean_dec_ref_known(v___x_468_, 0);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_horizontalOrVertical___boxed(lean_object* v_terms_470_, lean_object* v_spacing_471_){
_start:
{
uint8_t v_spacing_boxed_472_; lean_object* v_res_473_; 
v_spacing_boxed_472_ = lean_unbox(v_spacing_471_);
v_res_473_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_470_, v_spacing_boxed_472_);
lean_dec_ref(v_terms_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(uint8_t v_x_474_){
_start:
{
switch(v_x_474_)
{
case 0:
{
lean_object* v___x_475_; 
v___x_475_ = lean_unsigned_to_nat(0u);
return v___x_475_;
}
case 1:
{
lean_object* v___x_476_; 
v___x_476_ = lean_unsigned_to_nat(1u);
return v___x_476_;
}
default: 
{
lean_object* v___x_477_; 
v___x_477_ = lean_unsigned_to_nat(2u);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx___boxed(lean_object* v_x_478_){
_start:
{
uint8_t v_x_boxed_479_; lean_object* v_res_480_; 
v_x_boxed_479_ = lean_unbox(v_x_478_);
v_res_480_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorIdx(v_x_boxed_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(lean_object* v_k_481_){
_start:
{
lean_inc(v_k_481_);
return v_k_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg___boxed(lean_object* v_k_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___redArg(v_k_482_);
lean_dec(v_k_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(lean_object* v_motive_484_, lean_object* v_ctorIdx_485_, uint8_t v_t_486_, lean_object* v_h_487_, lean_object* v_k_488_){
_start:
{
lean_inc(v_k_488_);
return v_k_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim___boxed(lean_object* v_motive_489_, lean_object* v_ctorIdx_490_, lean_object* v_t_491_, lean_object* v_h_492_, lean_object* v_k_493_){
_start:
{
uint8_t v_t_boxed_494_; lean_object* v_res_495_; 
v_t_boxed_494_ = lean_unbox(v_t_491_);
v_res_495_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_ctorElim(v_motive_489_, v_ctorIdx_490_, v_t_boxed_494_, v_h_492_, v_k_493_);
lean_dec(v_k_493_);
lean_dec(v_ctorIdx_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(lean_object* v_includeTrailingSep_496_){
_start:
{
lean_inc(v_includeTrailingSep_496_);
return v_includeTrailingSep_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg___boxed(lean_object* v_includeTrailingSep_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___redArg(v_includeTrailingSep_497_);
lean_dec(v_includeTrailingSep_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(lean_object* v_motive_499_, uint8_t v_t_500_, lean_object* v_h_501_, lean_object* v_includeTrailingSep_502_){
_start:
{
lean_inc(v_includeTrailingSep_502_);
return v_includeTrailingSep_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim___boxed(lean_object* v_motive_503_, lean_object* v_t_504_, lean_object* v_h_505_, lean_object* v_includeTrailingSep_506_){
_start:
{
uint8_t v_t_boxed_507_; lean_object* v_res_508_; 
v_t_boxed_507_ = lean_unbox(v_t_504_);
v_res_508_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_includeTrailingSep_elim(v_motive_503_, v_t_boxed_507_, v_h_505_, v_includeTrailingSep_506_);
lean_dec(v_includeTrailingSep_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(lean_object* v_excludeTrailingSep_509_){
_start:
{
lean_inc(v_excludeTrailingSep_509_);
return v_excludeTrailingSep_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg___boxed(lean_object* v_excludeTrailingSep_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___redArg(v_excludeTrailingSep_510_);
lean_dec(v_excludeTrailingSep_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(lean_object* v_motive_512_, uint8_t v_t_513_, lean_object* v_h_514_, lean_object* v_excludeTrailingSep_515_){
_start:
{
lean_inc(v_excludeTrailingSep_515_);
return v_excludeTrailingSep_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim___boxed(lean_object* v_motive_516_, lean_object* v_t_517_, lean_object* v_h_518_, lean_object* v_excludeTrailingSep_519_){
_start:
{
uint8_t v_t_boxed_520_; lean_object* v_res_521_; 
v_t_boxed_520_ = lean_unbox(v_t_517_);
v_res_521_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_excludeTrailingSep_elim(v_motive_516_, v_t_boxed_520_, v_h_518_, v_excludeTrailingSep_519_);
lean_dec(v_excludeTrailingSep_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(lean_object* v_retainTrailingSep_522_){
_start:
{
lean_inc(v_retainTrailingSep_522_);
return v_retainTrailingSep_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg___boxed(lean_object* v_retainTrailingSep_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___redArg(v_retainTrailingSep_523_);
lean_dec(v_retainTrailingSep_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(lean_object* v_motive_525_, uint8_t v_t_526_, lean_object* v_h_527_, lean_object* v_retainTrailingSep_528_){
_start:
{
lean_inc(v_retainTrailingSep_528_);
return v_retainTrailingSep_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim___boxed(lean_object* v_motive_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_retainTrailingSep_532_){
_start:
{
uint8_t v_t_boxed_533_; lean_object* v_res_534_; 
v_t_boxed_533_ = lean_unbox(v_t_530_);
v_res_534_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_TrailingSep_retainTrailingSep_elim(v_motive_529_, v_t_boxed_533_, v_h_531_, v_retainTrailingSep_532_);
lean_dec(v_retainTrailingSep_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(lean_object* v_x_535_){
_start:
{
switch(lean_obj_tag(v_x_535_))
{
case 0:
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(0u);
return v___x_536_;
}
case 1:
{
lean_object* v___x_537_; 
v___x_537_ = lean_unsigned_to_nat(1u);
return v___x_537_;
}
case 2:
{
lean_object* v___x_538_; 
v___x_538_ = lean_unsigned_to_nat(2u);
return v___x_538_;
}
default: 
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(3u);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx___boxed(lean_object* v_x_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorIdx(v_x_540_);
lean_dec_ref(v_x_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(lean_object* v_t_542_, lean_object* v_k_543_){
_start:
{
switch(lean_obj_tag(v_t_542_))
{
case 1:
{
uint8_t v_allowFlattening_544_; lean_object* v_afterElem_x3f_545_; uint8_t v_trailingSep_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_allowFlattening_544_ = lean_ctor_get_uint8(v_t_542_, sizeof(void*)*1);
v_afterElem_x3f_545_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_afterElem_x3f_545_);
v_trailingSep_546_ = lean_ctor_get_uint8(v_t_542_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_542_, 1);
v___x_547_ = lean_box(v_allowFlattening_544_);
v___x_548_ = lean_box(v_trailingSep_546_);
v___x_549_ = lean_apply_3(v_k_543_, v___x_547_, v_afterElem_x3f_545_, v___x_548_);
return v___x_549_;
}
case 3:
{
lean_object* v_afterElem_x3f_550_; uint8_t v_trailingSep_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_afterElem_x3f_550_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_afterElem_x3f_550_);
v_trailingSep_551_ = lean_ctor_get_uint8(v_t_542_, sizeof(void*)*1);
lean_dec_ref_known(v_t_542_, 1);
v___x_552_ = lean_box(v_trailingSep_551_);
v___x_553_ = lean_apply_2(v_k_543_, v_afterElem_x3f_550_, v___x_552_);
return v___x_553_;
}
default: 
{
lean_object* v_afterElem_x3f_554_; lean_object* v_afterSep_x3f_555_; uint8_t v_trailingSep_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_afterElem_x3f_554_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_afterElem_x3f_554_);
v_afterSep_x3f_555_ = lean_ctor_get(v_t_542_, 1);
lean_inc(v_afterSep_x3f_555_);
v_trailingSep_556_ = lean_ctor_get_uint8(v_t_542_, sizeof(void*)*2);
lean_dec_ref(v_t_542_);
v___x_557_ = lean_box(v_trailingSep_556_);
v___x_558_ = lean_apply_3(v_k_543_, v_afterElem_x3f_554_, v_afterSep_x3f_555_, v___x_557_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(lean_object* v_motive_559_, lean_object* v_ctorIdx_560_, lean_object* v_t_561_, lean_object* v_h_562_, lean_object* v_k_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_561_, v_k_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___boxed(lean_object* v_motive_565_, lean_object* v_ctorIdx_566_, lean_object* v_t_567_, lean_object* v_h_568_, lean_object* v_k_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim(v_motive_565_, v_ctorIdx_566_, v_t_567_, v_h_568_, v_k_569_);
lean_dec(v_ctorIdx_566_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim___redArg(lean_object* v_t_571_, lean_object* v_joinUsingSep_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_571_, v_joinUsingSep_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingSep_elim(lean_object* v_motive_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_joinUsingSep_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_575_, v_joinUsingSep_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim___redArg(lean_object* v_t_579_, lean_object* v_joinUsingNl_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_579_, v_joinUsingNl_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_joinUsingNl_elim(lean_object* v_motive_582_, lean_object* v_t_583_, lean_object* v_h_584_, lean_object* v_joinUsingNl_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_583_, v_joinUsingNl_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim___redArg(lean_object* v_t_587_, lean_object* v_fillUsingSep_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_587_, v_fillUsingSep_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSep_elim(lean_object* v_motive_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_fillUsingSep_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_591_, v_fillUsingSep_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim___redArg(lean_object* v_t_595_, lean_object* v_fillUsingSpacedSep_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_595_, v_fillUsingSpacedSep_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_fillUsingSpacedSep_elim(lean_object* v_motive_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_fillUsingSpacedSep_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_ctorElim___redArg(v_t_599_, v_fillUsingSpacedSep_601_);
return v___x_602_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(lean_object* v_x_603_){
_start:
{
switch(lean_obj_tag(v_x_603_))
{
case 1:
{
uint8_t v_trailingSep_604_; 
v_trailingSep_604_ = lean_ctor_get_uint8(v_x_603_, sizeof(void*)*1 + 1);
return v_trailingSep_604_;
}
case 3:
{
uint8_t v_trailingSep_605_; 
v_trailingSep_605_ = lean_ctor_get_uint8(v_x_603_, sizeof(void*)*1);
return v_trailingSep_605_;
}
default: 
{
uint8_t v_trailingSep_606_; 
v_trailingSep_606_ = lean_ctor_get_uint8(v_x_603_, sizeof(void*)*2);
return v_trailingSep_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep___boxed(lean_object* v_x_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Lean_Fmt_Layouts_Types_SepArrayFormat_trailingSep(v_x_607_);
lean_dec_ref(v_x_607_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(lean_object* v_sepArray_610_, lean_object* v_sep_611_, lean_object* v___x_612_, uint8_t v_trailingSep_613_, lean_object* v_a_614_, lean_object* v_b_615_){
_start:
{
lean_object* v_inner_616_; lean_object* v_next_617_; 
v_inner_616_ = lean_ctor_get(v_a_614_, 2);
lean_inc(v_inner_616_);
v_next_617_ = lean_ctor_get(v_inner_616_, 0);
lean_inc(v_next_617_);
if (lean_obj_tag(v_next_617_) == 0)
{
lean_dec(v_inner_616_);
lean_dec_ref(v_a_614_);
lean_dec_ref(v_sep_611_);
return v_b_615_;
}
else
{
lean_object* v_nextIdx_618_; lean_object* v_n_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_670_; 
v_nextIdx_618_ = lean_ctor_get(v_a_614_, 0);
v_n_619_ = lean_ctor_get(v_a_614_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_614_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v_a_614_, 2);
lean_dec(v_unused_671_);
v___x_621_ = v_a_614_;
v_isShared_622_ = v_isSharedCheck_670_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_n_619_);
lean_inc(v_nextIdx_618_);
lean_dec(v_a_614_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_670_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_upperBound_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_668_; 
v_upperBound_623_ = lean_ctor_get(v_inner_616_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_inner_616_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_inner_616_, 0);
lean_dec(v_unused_669_);
v___x_625_ = v_inner_616_;
v_isShared_626_ = v_isSharedCheck_668_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_upperBound_623_);
lean_dec(v_inner_616_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_668_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_667_; 
v_val_627_ = lean_ctor_get(v_next_617_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_next_617_);
if (v_isSharedCheck_667_ == 0)
{
v___x_629_ = v_next_617_;
v_isShared_630_ = v_isSharedCheck_667_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_dec(v_next_617_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_667_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_nat_add(v_val_627_, v_nextIdx_618_);
lean_dec(v_nextIdx_618_);
lean_dec(v_val_627_);
v___x_632_ = lean_nat_dec_lt(v___x_631_, v_upperBound_623_);
if (v___x_632_ == 0)
{
lean_dec(v___x_631_);
lean_del_object(v___x_629_);
lean_del_object(v___x_625_);
lean_dec(v_upperBound_623_);
lean_del_object(v___x_621_);
lean_dec(v_n_619_);
lean_dec_ref(v_sep_611_);
return v_b_615_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_633_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v___x_631_, v___x_634_);
lean_inc(v___x_635_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_635_);
v___x_637_ = v___x_629_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_666_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_637_);
v___x_639_ = v___x_625_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_upperBound_623_);
v___x_639_ = v_reuseFailAlloc_665_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
lean_inc(v_n_619_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 2, v___x_639_);
lean_ctor_set(v___x_621_, 0, v_n_619_);
v___x_641_ = v___x_621_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_n_619_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_n_619_);
lean_ctor_set(v_reuseFailAlloc_664_, 2, v___x_639_);
v___x_641_ = v_reuseFailAlloc_664_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_array_get_borrowed(v___x_633_, v_sepArray_610_, v___x_631_);
v___x_643_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___y_646_; lean_object* v___y_650_; uint8_t v___y_655_; 
lean_inc(v___x_642_);
v___x_644_ = lean_array_push(v_b_615_, v___x_642_);
if (v_trailingSep_613_ == 2)
{
goto v___jp_660_;
}
else
{
if (v___x_643_ == 0)
{
lean_dec(v___x_631_);
v___y_655_ = v___x_643_;
goto v___jp_654_;
}
else
{
goto v___jp_660_;
}
}
v___jp_645_:
{
lean_object* v___x_647_; 
v___x_647_ = lean_array_push(v___x_644_, v___y_646_);
v_a_614_ = v___x_641_;
v_b_615_ = v___x_647_;
goto _start;
}
v___jp_649_:
{
uint8_t v___x_651_; 
v___x_651_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_650_);
if (v___x_651_ == 0)
{
v___y_646_ = v___y_650_;
goto v___jp_645_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec_ref(v___y_650_);
lean_inc_ref(v_sep_611_);
v___x_652_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_611_);
v___x_653_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_652_);
v___y_646_ = v___x_653_;
goto v___jp_645_;
}
}
v___jp_654_:
{
if (v___y_655_ == 0)
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_array_get_size(v_sepArray_610_);
v___x_657_ = lean_nat_dec_lt(v___x_635_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v___x_635_);
v___x_658_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_650_ = v___x_658_;
goto v___jp_649_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = lean_array_fget_borrowed(v_sepArray_610_, v___x_635_);
lean_dec(v___x_635_);
lean_inc(v___x_659_);
v___y_650_ = v___x_659_;
goto v___jp_649_;
}
}
else
{
lean_dec_ref(v___x_641_);
lean_dec(v___x_635_);
lean_dec_ref(v_sep_611_);
return v___x_644_;
}
}
v___jp_660_:
{
lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_661_ = lean_nat_sub(v___x_612_, v___x_634_);
v___x_662_ = lean_nat_dec_eq(v___x_631_, v___x_661_);
lean_dec(v___x_661_);
lean_dec(v___x_631_);
v___y_655_ = v___x_662_;
goto v___jp_654_;
}
}
else
{
lean_dec(v___x_635_);
lean_dec(v___x_631_);
v_a_614_ = v___x_641_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg___boxed(lean_object* v_sepArray_672_, lean_object* v_sep_673_, lean_object* v___x_674_, lean_object* v_trailingSep_675_, lean_object* v_a_676_, lean_object* v_b_677_){
_start:
{
uint8_t v_trailingSep_boxed_678_; lean_object* v_res_679_; 
v_trailingSep_boxed_678_ = lean_unbox(v_trailingSep_675_);
v_res_679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_672_, v_sep_673_, v___x_674_, v_trailingSep_boxed_678_, v_a_676_, v_b_677_);
lean_dec(v___x_674_);
lean_dec_ref(v_sepArray_672_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(lean_object* v_sep_682_, lean_object* v_sepArray_683_, uint8_t v_trailingSep_684_){
_start:
{
lean_object* v___x_685_; lean_object* v_r_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_685_ = lean_unsigned_to_nat(0u);
v_r_686_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_687_ = lean_array_get_size(v_sepArray_683_);
v___x_688_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___closed__0));
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_691_, 0, v___x_685_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
lean_ctor_set(v___x_691_, 2, v___x_689_);
v___x_692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_683_, v_sep_682_, v___x_687_, v_trailingSep_684_, v___x_691_, v_r_686_);
if (v_trailingSep_684_ == 1)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_693_ = lean_unsigned_to_nat(2u);
v___x_694_ = lean_array_get_size(v___x_692_);
v___x_695_ = lean_nat_mod(v___x_694_, v___x_693_);
v___x_696_ = lean_nat_dec_eq(v___x_695_, v___x_685_);
lean_dec(v___x_695_);
if (v___x_696_ == 0)
{
return v___x_692_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = lean_array_pop(v___x_692_);
return v___x_697_;
}
}
else
{
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize___boxed(lean_object* v_sep_698_, lean_object* v_sepArray_699_, lean_object* v_trailingSep_700_){
_start:
{
uint8_t v_trailingSep_boxed_701_; lean_object* v_res_702_; 
v_trailingSep_boxed_701_ = lean_unbox(v_trailingSep_700_);
v_res_702_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_698_, v_sepArray_699_, v_trailingSep_boxed_701_);
lean_dec_ref(v_sepArray_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(lean_object* v_sepArray_703_, lean_object* v_sep_704_, lean_object* v___x_705_, uint8_t v_trailingSep_706_, lean_object* v_inst_707_, lean_object* v_R_708_, lean_object* v_a_709_, lean_object* v_b_710_, lean_object* v_c_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___redArg(v_sepArray_703_, v_sep_704_, v___x_705_, v_trailingSep_706_, v_a_709_, v_b_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0___boxed(lean_object* v_sepArray_713_, lean_object* v_sep_714_, lean_object* v___x_715_, lean_object* v_trailingSep_716_, lean_object* v_inst_717_, lean_object* v_R_718_, lean_object* v_a_719_, lean_object* v_b_720_, lean_object* v_c_721_){
_start:
{
uint8_t v_trailingSep_boxed_722_; lean_object* v_res_723_; 
v_trailingSep_boxed_722_ = lean_unbox(v_trailingSep_716_);
v_res_723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize_spec__0(v_sepArray_713_, v_sep_714_, v___x_715_, v_trailingSep_boxed_722_, v_inst_717_, v_R_718_, v_a_719_, v_b_720_, v_c_721_);
lean_dec(v___x_715_);
lean_dec_ref(v_sepArray_713_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(lean_object* v_sepArray_724_, lean_object* v_sep_725_, lean_object* v_afterSep_x3f_726_, lean_object* v_afterElem_x3f_727_, size_t v_sz_728_, size_t v_i_729_, lean_object* v_bs_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_729_, v_sz_728_);
if (v___x_731_ == 0)
{
lean_dec(v_afterElem_x3f_727_);
lean_dec(v_afterSep_x3f_726_);
lean_dec_ref(v_sep_725_);
return v_bs_730_;
}
else
{
lean_object* v_v_732_; lean_object* v___x_733_; lean_object* v_bs_x27_734_; lean_object* v___y_736_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_v_732_ = lean_array_uget(v_bs_730_, v_i_729_);
v___x_733_ = lean_unsigned_to_nat(0u);
v_bs_x27_734_ = lean_array_uset(v_bs_730_, v_i_729_, v___x_733_);
v___x_755_ = lean_usize_to_nat(v_i_729_);
v___x_756_ = lean_array_get_size(v_sepArray_724_);
v___x_757_ = lean_unsigned_to_nat(1u);
v___x_758_ = lean_nat_sub(v___x_756_, v___x_757_);
v___x_759_ = lean_nat_dec_eq(v___x_755_, v___x_758_);
lean_dec(v___x_758_);
if (v___x_759_ == 0)
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v_isElem_762_; lean_object* v___y_764_; 
v___x_760_ = lean_unsigned_to_nat(2u);
v___x_761_ = lean_nat_mod(v___x_755_, v___x_760_);
lean_dec(v___x_755_);
v_isElem_762_ = lean_nat_dec_eq(v___x_761_, v___x_733_);
lean_dec(v___x_761_);
if (v_isElem_762_ == 0)
{
lean_inc(v_afterSep_x3f_726_);
v___y_764_ = v_afterSep_x3f_726_;
goto v___jp_763_;
}
else
{
lean_inc(v_afterElem_x3f_727_);
v___y_764_ = v_afterElem_x3f_727_;
goto v___jp_763_;
}
v___jp_763_:
{
if (v_isElem_762_ == 0)
{
uint8_t v___x_765_; 
v___x_765_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_732_);
if (v___x_765_ == 0)
{
v___y_742_ = v___y_764_;
v___y_743_ = v_v_732_;
goto v___jp_741_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_v_732_);
lean_inc_ref(v_sep_725_);
v___x_766_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_725_);
v___x_767_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_766_);
v___y_742_ = v___y_764_;
v___y_743_ = v___x_767_;
goto v___jp_741_;
}
}
else
{
v___y_742_ = v___y_764_;
v___y_743_ = v_v_732_;
goto v___jp_741_;
}
}
}
else
{
lean_dec(v___x_755_);
v___y_736_ = v_v_732_;
goto v___jp_735_;
}
v___jp_735_:
{
size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_add(v_i_729_, v___x_737_);
v___x_739_ = lean_array_uset(v_bs_x27_734_, v_i_729_, v___y_736_);
v_i_729_ = v___x_738_;
v_bs_730_ = v___x_739_;
goto _start;
}
v___jp_741_:
{
if (lean_obj_tag(v___y_742_) == 1)
{
lean_object* v_val_744_; uint8_t v___x_745_; 
v_val_744_ = lean_ctor_get(v___y_742_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v___y_742_, 1);
v___x_745_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_743_);
if (v___x_745_ == 0)
{
uint8_t v___x_746_; 
v___x_746_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_744_);
if (v___x_746_ == 0)
{
lean_object* v_doc_747_; lean_object* v_doc_748_; uint8_t v___x_749_; 
v_doc_747_ = lean_ctor_get(v___y_743_, 0);
lean_inc(v_doc_747_);
lean_dec_ref(v___y_743_);
v_doc_748_ = lean_ctor_get(v_val_744_, 0);
lean_inc(v_doc_748_);
lean_dec(v_val_744_);
v___x_749_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_747_);
if (v___x_749_ == 0)
{
uint8_t v___x_750_; 
v___x_750_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_748_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_747_, v_doc_748_);
v___x_752_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_751_);
v___y_736_ = v___x_752_;
goto v___jp_735_;
}
else
{
lean_object* v___x_753_; 
lean_dec(v_doc_748_);
v___x_753_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_747_);
v___y_736_ = v___x_753_;
goto v___jp_735_;
}
}
else
{
lean_object* v___x_754_; 
lean_dec(v_doc_747_);
v___x_754_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_748_);
v___y_736_ = v___x_754_;
goto v___jp_735_;
}
}
else
{
lean_dec(v_val_744_);
v___y_736_ = v___y_743_;
goto v___jp_735_;
}
}
else
{
lean_dec_ref(v___y_743_);
v___y_736_ = v_val_744_;
goto v___jp_735_;
}
}
else
{
lean_dec(v___y_742_);
v___y_736_ = v___y_743_;
goto v___jp_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg___boxed(lean_object* v_sepArray_768_, lean_object* v_sep_769_, lean_object* v_afterSep_x3f_770_, lean_object* v_afterElem_x3f_771_, lean_object* v_sz_772_, lean_object* v_i_773_, lean_object* v_bs_774_){
_start:
{
size_t v_sz_boxed_775_; size_t v_i_boxed_776_; lean_object* v_res_777_; 
v_sz_boxed_775_ = lean_unbox_usize(v_sz_772_);
lean_dec(v_sz_772_);
v_i_boxed_776_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_768_, v_sep_769_, v_afterSep_x3f_770_, v_afterElem_x3f_771_, v_sz_boxed_775_, v_i_boxed_776_, v_bs_774_);
lean_dec_ref(v_sepArray_768_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(lean_object* v_sep_778_, lean_object* v_sepArray_779_, lean_object* v_afterElem_x3f_780_, lean_object* v_afterSep_x3f_781_){
_start:
{
size_t v_sz_782_; size_t v___x_783_; lean_object* v_docs_784_; lean_object* v___x_785_; 
v_sz_782_ = lean_array_size(v_sepArray_779_);
v___x_783_ = ((size_t)0ULL);
lean_inc_ref(v_sepArray_779_);
v_docs_784_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_779_, v_sep_778_, v_afterSep_x3f_781_, v_afterElem_x3f_780_, v_sz_782_, v___x_783_, v_sepArray_779_);
lean_dec_ref(v_sepArray_779_);
v___x_785_ = l_Lean_Fmt_TaggedDoc_join(v_docs_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(lean_object* v_sepArray_786_, lean_object* v_sep_787_, lean_object* v_afterSep_x3f_788_, lean_object* v_afterElem_x3f_789_, lean_object* v_as_790_, size_t v_sz_791_, size_t v_i_792_, lean_object* v_bs_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___redArg(v_sepArray_786_, v_sep_787_, v_afterSep_x3f_788_, v_afterElem_x3f_789_, v_sz_791_, v_i_792_, v_bs_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0___boxed(lean_object* v_sepArray_795_, lean_object* v_sep_796_, lean_object* v_afterSep_x3f_797_, lean_object* v_afterElem_x3f_798_, lean_object* v_as_799_, lean_object* v_sz_800_, lean_object* v_i_801_, lean_object* v_bs_802_){
_start:
{
size_t v_sz_boxed_803_; size_t v_i_boxed_804_; lean_object* v_res_805_; 
v_sz_boxed_803_ = lean_unbox_usize(v_sz_800_);
lean_dec(v_sz_800_);
v_i_boxed_804_ = lean_unbox_usize(v_i_801_);
lean_dec(v_i_801_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep_spec__0(v_sepArray_795_, v_sep_796_, v_afterSep_x3f_797_, v_afterElem_x3f_798_, v_as_799_, v_sz_boxed_803_, v_i_boxed_804_, v_bs_802_);
lean_dec_ref(v_as_799_);
lean_dec_ref(v_sepArray_795_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(lean_object* v_upperBound_806_, lean_object* v___x_807_, lean_object* v_sep_808_, lean_object* v_a_809_, lean_object* v_b_810_){
_start:
{
lean_object* v_a_812_; uint8_t v___x_816_; 
v___x_816_ = lean_nat_dec_lt(v_a_809_, v_upperBound_806_);
if (v___x_816_ == 0)
{
lean_dec(v_a_809_);
lean_dec_ref(v_sep_808_);
return v_b_810_;
}
else
{
lean_object* v_fst_817_; lean_object* v_snd_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_838_; 
v_fst_817_ = lean_ctor_get(v_b_810_, 0);
v_snd_818_ = lean_ctor_get(v_b_810_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_b_810_);
if (v_isSharedCheck_838_ == 0)
{
v___x_820_ = v_b_810_;
v_isShared_821_ = v_isSharedCheck_838_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_snd_818_);
lean_inc(v_fst_817_);
lean_dec(v_b_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_838_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___y_823_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_array_fget_borrowed(v___x_807_, v_a_809_);
v___x_830_ = lean_unsigned_to_nat(2u);
v___x_831_ = lean_nat_mod(v_a_809_, v___x_830_);
v___x_832_ = lean_nat_dec_eq(v___x_831_, v___x_828_);
lean_dec(v___x_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; 
v___x_833_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_829_);
if (v___x_833_ == 0)
{
lean_inc(v___x_829_);
v___y_823_ = v___x_829_;
goto v___jp_822_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_inc_ref(v_sep_808_);
v___x_834_ = l_Lean_Fmt_Doc_text___override___redArg(v_sep_808_);
v___x_835_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_834_);
v___y_823_ = v___x_835_;
goto v___jp_822_;
}
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_del_object(v___x_820_);
lean_inc(v___x_829_);
v___x_836_ = lean_array_push(v_fst_817_, v___x_829_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v_snd_818_);
v_a_812_ = v___x_837_;
goto v___jp_811_;
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_826_; 
v___x_824_ = lean_array_push(v_snd_818_, v___y_823_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_824_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_fst_817_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v_a_812_ = v___x_826_;
goto v___jp_811_;
}
}
}
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v_a_809_, v___x_813_);
lean_dec(v_a_809_);
v_a_809_ = v___x_814_;
v_b_810_ = v_a_812_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg___boxed(lean_object* v_upperBound_839_, lean_object* v___x_840_, lean_object* v_sep_841_, lean_object* v_a_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_839_, v___x_840_, v_sep_841_, v_a_842_, v_b_843_);
lean_dec_ref(v___x_840_);
lean_dec(v_upperBound_839_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(lean_object* v_sep_847_, lean_object* v_sepArray_848_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_fst_853_; lean_object* v_snd_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_array_get_size(v_sepArray_848_);
v___x_851_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___closed__0));
v___x_852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v___x_850_, v_sepArray_848_, v_sep_847_, v___x_849_, v___x_851_);
v_fst_853_ = lean_ctor_get(v___x_852_, 0);
v_snd_854_ = lean_ctor_get(v___x_852_, 1);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_852_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_snd_854_);
lean_inc(v_fst_853_);
lean_dec(v___x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_fst_853_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_snd_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split___boxed(lean_object* v_sep_862_, lean_object* v_sepArray_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_862_, v_sepArray_863_);
lean_dec_ref(v_sepArray_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(lean_object* v_upperBound_865_, lean_object* v___x_866_, lean_object* v_sep_867_, lean_object* v_inst_868_, lean_object* v_R_869_, lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v_c_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___redArg(v_upperBound_865_, v___x_866_, v_sep_867_, v_a_870_, v_b_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0___boxed(lean_object* v_upperBound_874_, lean_object* v___x_875_, lean_object* v_sep_876_, lean_object* v_inst_877_, lean_object* v_R_878_, lean_object* v_a_879_, lean_object* v_b_880_, lean_object* v_c_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split_spec__0(v_upperBound_874_, v___x_875_, v_sep_876_, v_inst_877_, v_R_878_, v_a_879_, v_b_880_, v_c_881_);
lean_dec_ref(v___x_875_);
lean_dec(v_upperBound_874_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(lean_object* v_fst_883_, lean_object* v_val_884_, size_t v_sz_885_, size_t v_i_886_, lean_object* v_bs_887_){
_start:
{
uint8_t v___x_888_; 
v___x_888_ = lean_usize_dec_lt(v_i_886_, v_sz_885_);
if (v___x_888_ == 0)
{
lean_dec_ref(v_val_884_);
return v_bs_887_;
}
else
{
lean_object* v_v_889_; lean_object* v___x_890_; lean_object* v_bs_x27_891_; lean_object* v___y_893_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_v_889_ = lean_array_uget(v_bs_887_, v_i_886_);
v___x_890_ = lean_unsigned_to_nat(0u);
v_bs_x27_891_ = lean_array_uset(v_bs_887_, v_i_886_, v___x_890_);
v___x_898_ = lean_usize_to_nat(v_i_886_);
v___x_899_ = lean_array_get_size(v_fst_883_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_sub(v___x_899_, v___x_900_);
v___x_902_ = lean_nat_dec_eq(v___x_898_, v___x_901_);
lean_dec(v___x_901_);
lean_dec(v___x_898_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_889_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_val_884_);
if (v___x_904_ == 0)
{
lean_object* v_doc_905_; lean_object* v_doc_906_; uint8_t v___x_907_; 
v_doc_905_ = lean_ctor_get(v_v_889_, 0);
lean_inc(v_doc_905_);
lean_dec(v_v_889_);
v_doc_906_ = lean_ctor_get(v_val_884_, 0);
v___x_907_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_905_);
if (v___x_907_ == 0)
{
uint8_t v___x_908_; 
v___x_908_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_906_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc(v_doc_906_);
v___x_909_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_905_, v_doc_906_);
v___x_910_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_909_);
v___y_893_ = v___x_910_;
goto v___jp_892_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_905_);
v___y_893_ = v___x_911_;
goto v___jp_892_;
}
}
else
{
lean_object* v___x_912_; 
lean_dec(v_doc_905_);
lean_inc(v_doc_906_);
v___x_912_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_906_);
v___y_893_ = v___x_912_;
goto v___jp_892_;
}
}
else
{
v___y_893_ = v_v_889_;
goto v___jp_892_;
}
}
else
{
lean_dec(v_v_889_);
lean_inc_ref(v_val_884_);
v___y_893_ = v_val_884_;
goto v___jp_892_;
}
}
else
{
v___y_893_ = v_v_889_;
goto v___jp_892_;
}
v___jp_892_:
{
size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; 
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_886_, v___x_894_);
v___x_896_ = lean_array_uset(v_bs_x27_891_, v_i_886_, v___y_893_);
v_i_886_ = v___x_895_;
v_bs_887_ = v___x_896_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg___boxed(lean_object* v_fst_913_, lean_object* v_val_914_, lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_bs_917_){
_start:
{
size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_sz_boxed_918_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_919_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_913_, v_val_914_, v_sz_boxed_918_, v_i_boxed_919_, v_bs_917_);
lean_dec_ref(v_fst_913_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(lean_object* v_sep_921_, lean_object* v_sepArray_922_, lean_object* v_afterElem_x3f_923_){
_start:
{
lean_object* v_elems_925_; lean_object* v___x_928_; 
v___x_928_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_921_, v_sepArray_922_);
if (lean_obj_tag(v_afterElem_x3f_923_) == 1)
{
lean_object* v_fst_929_; lean_object* v_val_930_; size_t v_sz_931_; size_t v___x_932_; lean_object* v_elems_933_; 
v_fst_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_n(v_fst_929_, 2);
lean_dec_ref(v___x_928_);
v_val_930_ = lean_ctor_get(v_afterElem_x3f_923_, 0);
lean_inc(v_val_930_);
lean_dec_ref_known(v_afterElem_x3f_923_, 1);
v_sz_931_ = lean_array_size(v_fst_929_);
v___x_932_ = ((size_t)0ULL);
v_elems_933_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_929_, v_val_930_, v_sz_931_, v___x_932_, v_fst_929_);
lean_dec(v_fst_929_);
v_elems_925_ = v_elems_933_;
goto v___jp_924_;
}
else
{
lean_object* v_fst_934_; 
lean_dec(v_afterElem_x3f_923_);
v_fst_934_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_fst_934_);
lean_dec_ref(v___x_928_);
v_elems_925_ = v_fst_934_;
goto v___jp_924_;
}
v___jp_924_:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_927_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_926_, v_elems_925_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl___boxed(lean_object* v_sep_935_, lean_object* v_sepArray_936_, lean_object* v_afterElem_x3f_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_935_, v_sepArray_936_, v_afterElem_x3f_937_);
lean_dec_ref(v_sepArray_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(lean_object* v_fst_939_, lean_object* v_val_940_, lean_object* v_as_941_, size_t v_sz_942_, size_t v_i_943_, lean_object* v_bs_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___redArg(v_fst_939_, v_val_940_, v_sz_942_, v_i_943_, v_bs_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0___boxed(lean_object* v_fst_946_, lean_object* v_val_947_, lean_object* v_as_948_, lean_object* v_sz_949_, lean_object* v_i_950_, lean_object* v_bs_951_){
_start:
{
size_t v_sz_boxed_952_; size_t v_i_boxed_953_; lean_object* v_res_954_; 
v_sz_boxed_952_ = lean_unbox_usize(v_sz_949_);
lean_dec(v_sz_949_);
v_i_boxed_953_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl_spec__0(v_fst_946_, v_val_947_, v_as_948_, v_sz_boxed_952_, v_i_boxed_953_, v_bs_951_);
lean_dec_ref(v_as_948_);
lean_dec_ref(v_fst_946_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0___redArg(lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v_a_957_, lean_object* v_b_958_){
_start:
{
lean_object* v_array_959_; lean_object* v_start_960_; lean_object* v_stop_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1044_; 
v_array_959_ = lean_ctor_get(v_a_957_, 0);
v_start_960_ = lean_ctor_get(v_a_957_, 1);
v_stop_961_ = lean_ctor_get(v_a_957_, 2);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_a_957_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_963_ = v_a_957_;
v_isShared_964_ = v_isSharedCheck_1044_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_stop_961_);
lean_inc(v_start_960_);
lean_inc(v_array_959_);
lean_dec(v_a_957_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1044_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_lt(v_start_960_, v_stop_961_);
if (v___x_965_ == 0)
{
lean_del_object(v___x_963_);
lean_dec(v_stop_961_);
lean_dec(v_start_960_);
lean_dec_ref(v_array_959_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v___y_955_);
return v_b_958_;
}
else
{
lean_object* v_snd_966_; lean_object* v_snd_967_; lean_object* v_fst_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1042_; 
v_snd_966_ = lean_ctor_get(v_b_958_, 1);
lean_inc(v_snd_966_);
v_snd_967_ = lean_ctor_get(v_snd_966_, 1);
lean_inc(v_snd_967_);
v_fst_968_ = lean_ctor_get(v_b_958_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_b_958_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_b_958_, 1);
lean_dec(v_unused_1043_);
v___x_970_ = v_b_958_;
v_isShared_971_ = v_isSharedCheck_1042_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_fst_968_);
lean_dec(v_b_958_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1042_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_fst_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1040_; 
v_fst_972_ = lean_ctor_get(v_snd_966_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_snd_966_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_snd_966_, 1);
lean_dec(v_unused_1041_);
v___x_974_ = v_snd_966_;
v_isShared_975_ = v_isSharedCheck_1040_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_fst_972_);
lean_dec(v_snd_966_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1040_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_array_976_; lean_object* v_start_977_; lean_object* v_stop_978_; uint8_t v___x_979_; 
v_array_976_ = lean_ctor_get(v_snd_967_, 0);
v_start_977_ = lean_ctor_get(v_snd_967_, 1);
v_stop_978_ = lean_ctor_get(v_snd_967_, 2);
v___x_979_ = lean_nat_dec_lt(v_start_977_, v_stop_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_981_; 
lean_del_object(v___x_963_);
lean_dec(v_stop_961_);
lean_dec(v_start_960_);
lean_dec_ref(v_array_959_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v___y_955_);
if (v_isShared_975_ == 0)
{
v___x_981_ = v___x_974_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_fst_972_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_snd_967_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_981_);
v___x_983_ = v___x_970_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_fst_968_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1036_; 
lean_inc(v_stop_978_);
lean_inc(v_start_977_);
lean_inc_ref(v_array_976_);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_snd_967_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; lean_object* v_unused_1038_; lean_object* v_unused_1039_; 
v_unused_1037_ = lean_ctor_get(v_snd_967_, 2);
lean_dec(v_unused_1037_);
v_unused_1038_ = lean_ctor_get(v_snd_967_, 1);
lean_dec(v_unused_1038_);
v_unused_1039_ = lean_ctor_get(v_snd_967_, 0);
lean_dec(v_unused_1039_);
v___x_987_ = v_snd_967_;
v_isShared_988_ = v_isSharedCheck_1036_;
goto v_resetjp_986_;
}
else
{
lean_dec(v_snd_967_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1036_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_add(v_start_960_, v___x_989_);
lean_inc_ref(v_array_959_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 2, v_stop_961_);
lean_ctor_set(v___x_987_, 1, v___x_990_);
lean_ctor_set(v___x_987_, 0, v_array_959_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_array_959_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_stop_961_);
v___x_992_ = v_reuseFailAlloc_1035_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_993_ = lean_array_fget(v_array_959_, v_start_960_);
lean_dec(v_start_960_);
lean_dec_ref(v_array_959_);
v___x_994_ = lean_array_fget(v_array_976_, v_start_977_);
v___x_995_ = lean_nat_add(v_start_977_, v___x_989_);
lean_dec(v_start_977_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 2, v_stop_978_);
lean_ctor_set(v___x_963_, 1, v___x_995_);
lean_ctor_set(v___x_963_, 0, v_array_976_);
v___x_997_ = v___x_963_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_array_976_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_stop_978_);
v___x_997_ = v_reuseFailAlloc_1034_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_998_ = lean_unsigned_to_nat(2u);
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_998_);
lean_inc(v_fst_968_);
lean_inc_ref(v___x_999_);
v___x_1000_ = lean_array_push(v___x_999_, v_fst_968_);
v___x_1001_ = lean_array_push(v___x_1000_, v_fst_972_);
v___x_1002_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1001_);
lean_inc(v___x_993_);
v___x_1003_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_993_);
v___x_1004_ = lean_unsigned_to_nat(5u);
v___x_1005_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1006_ = lean_array_push(v___x_1005_, v_fst_968_);
lean_inc_ref_n(v___y_955_, 2);
v___x_1007_ = lean_array_push(v___x_1006_, v___y_955_);
lean_inc(v___x_994_);
v___x_1008_ = lean_array_push(v___x_1007_, v___x_994_);
lean_inc_ref_n(v___y_956_, 2);
v___x_1009_ = lean_array_push(v___x_1008_, v___y_956_);
lean_inc_ref(v___x_1003_);
v___x_1010_ = lean_array_push(v___x_1009_, v___x_1003_);
v___x_1011_ = l_Lean_Fmt_TaggedDoc_join(v___x_1010_);
v___x_1012_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1013_ = lean_unsigned_to_nat(6u);
v___x_1014_ = lean_mk_empty_array_with_capacity(v___x_1013_);
v___x_1015_ = lean_array_push(v___x_1014_, v___x_1002_);
v___x_1016_ = lean_array_push(v___x_1015_, v___y_955_);
v___x_1017_ = lean_array_push(v___x_1016_, v___x_994_);
v___x_1018_ = lean_array_push(v___x_1017_, v___y_956_);
v___x_1019_ = lean_array_push(v___x_1018_, v___x_1012_);
lean_inc_ref(v___x_1019_);
v___x_1020_ = lean_array_push(v___x_1019_, v___x_1003_);
v___x_1021_ = l_Lean_Fmt_TaggedDoc_join(v___x_1020_);
v___x_1022_ = lean_array_push(v___x_999_, v___x_1011_);
v___x_1023_ = lean_array_push(v___x_1022_, v___x_1021_);
v___x_1024_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1023_);
v___x_1025_ = lean_array_push(v___x_1019_, v___x_993_);
v___x_1026_ = l_Lean_Fmt_TaggedDoc_join(v___x_1025_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v___x_997_);
lean_ctor_set(v___x_974_, 0, v___x_1026_);
v___x_1028_ = v___x_974_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___x_997_);
v___x_1028_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_1028_);
lean_ctor_set(v___x_970_, 0, v___x_1024_);
v___x_1030_ = v___x_970_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
v_a_957_ = v___x_992_;
v_b_958_ = v___x_1030_;
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(lean_object* v_sep_1045_, lean_object* v_sepArray_1046_, lean_object* v_afterElem_x3f_1047_, lean_object* v_afterSep_x3f_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_elems_1054_; lean_object* v_seps_1055_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1110_; 
v___x_1049_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (lean_obj_tag(v_afterElem_x3f_1047_) == 0)
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1110_ = v___x_1113_;
goto v___jp_1109_;
}
else
{
lean_object* v_val_1114_; 
v_val_1114_ = lean_ctor_get(v_afterElem_x3f_1047_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v_afterElem_x3f_1047_, 1);
v___y_1110_ = v_val_1114_;
goto v___jp_1109_;
}
v___jp_1050_:
{
lean_object* v_lastNotFlattened_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_lastNotFlattened_1056_ = lean_array_get(v___x_1049_, v_elems_1054_, v___y_1051_);
v___x_1057_ = lean_array_get_size(v_elems_1054_);
v___x_1058_ = lean_unsigned_to_nat(1u);
v___x_1059_ = lean_nat_dec_eq(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v_lastFlattened_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_snd_1067_; lean_object* v_fst_1068_; lean_object* v_fst_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
lean_inc(v_lastNotFlattened_1056_);
v_lastFlattened_1060_ = l_Lean_Fmt_TaggedDoc_flattened(v_lastNotFlattened_1056_);
v___x_1061_ = lean_array_get_size(v_seps_1055_);
v___x_1062_ = l_Array_toSubarray___redArg(v_seps_1055_, v___y_1051_, v___x_1061_);
v___x_1063_ = l_Array_toSubarray___redArg(v_elems_1054_, v___x_1058_, v___x_1057_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v_lastNotFlattened_1056_);
lean_ctor_set(v___x_1064_, 1, v___x_1062_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_lastFlattened_1060_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0___redArg(v___y_1052_, v___y_1053_, v___x_1063_, v___x_1065_);
v_snd_1067_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_snd_1067_);
v_fst_1068_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_fst_1068_);
lean_dec_ref(v___x_1066_);
v_fst_1069_ = lean_ctor_get(v_snd_1067_, 0);
lean_inc(v_fst_1069_);
lean_dec(v_snd_1067_);
v___x_1070_ = lean_unsigned_to_nat(2u);
v___x_1071_ = lean_mk_empty_array_with_capacity(v___x_1070_);
v___x_1072_ = lean_array_push(v___x_1071_, v_fst_1068_);
v___x_1073_ = lean_array_push(v___x_1072_, v_fst_1069_);
v___x_1074_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1073_);
return v___x_1074_;
}
else
{
lean_dec_ref(v_seps_1055_);
lean_dec_ref(v_elems_1054_);
lean_dec_ref(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
return v_lastNotFlattened_1056_;
}
}
v___jp_1075_:
{
lean_object* v_seps_1081_; 
v_seps_1081_ = lean_array_pop(v___y_1079_);
v___y_1051_ = v___y_1076_;
v___y_1052_ = v___y_1077_;
v___y_1053_ = v___y_1078_;
v_elems_1054_ = v___y_1080_;
v_seps_1055_ = v_seps_1081_;
goto v___jp_1050_;
}
v___jp_1082_:
{
lean_object* v___x_1085_; lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1085_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_1045_, v_sepArray_1046_);
v_fst_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_fst_1086_);
v_snd_1087_ = lean_ctor_get(v___x_1085_, 1);
lean_inc(v_snd_1087_);
lean_dec_ref(v___x_1085_);
v___x_1088_ = lean_array_get_size(v_fst_1086_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_nat_dec_eq(v___x_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_array_get_size(v_snd_1087_);
v___x_1092_ = lean_nat_dec_eq(v___x_1091_, v___x_1088_);
if (v___x_1092_ == 0)
{
v___y_1051_ = v___x_1089_;
v___y_1052_ = v___y_1083_;
v___y_1053_ = v___y_1084_;
v_elems_1054_ = v_fst_1086_;
v_seps_1055_ = v_snd_1087_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_sub(v___x_1088_, v___x_1093_);
v___x_1095_ = lean_nat_dec_lt(v___x_1094_, v___x_1088_);
if (v___x_1095_ == 0)
{
lean_dec(v___x_1094_);
v___y_1076_ = v___x_1089_;
v___y_1077_ = v___y_1083_;
v___y_1078_ = v___y_1084_;
v___y_1079_ = v_snd_1087_;
v___y_1080_ = v_fst_1086_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1096_; lean_object* v_trailingSep_1097_; lean_object* v_v_1098_; lean_object* v___x_1099_; lean_object* v_xs_x27_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1096_ = lean_nat_sub(v___x_1091_, v___x_1093_);
v_trailingSep_1097_ = lean_array_get_borrowed(v___x_1049_, v_snd_1087_, v___x_1096_);
lean_dec(v___x_1096_);
v_v_1098_ = lean_array_fget(v_fst_1086_, v___x_1094_);
v___x_1099_ = lean_box(0);
v_xs_x27_1100_ = lean_array_fset(v_fst_1086_, v___x_1094_, v___x_1099_);
v___x_1101_ = lean_unsigned_to_nat(3u);
v___x_1102_ = lean_mk_empty_array_with_capacity(v___x_1101_);
v___x_1103_ = lean_array_push(v___x_1102_, v_v_1098_);
lean_inc_ref(v___y_1083_);
v___x_1104_ = lean_array_push(v___x_1103_, v___y_1083_);
lean_inc(v_trailingSep_1097_);
v___x_1105_ = lean_array_push(v___x_1104_, v_trailingSep_1097_);
v___x_1106_ = l_Lean_Fmt_TaggedDoc_join(v___x_1105_);
v___x_1107_ = lean_array_fset(v_xs_x27_1100_, v___x_1094_, v___x_1106_);
lean_dec(v___x_1094_);
v___y_1076_ = v___x_1089_;
v___y_1077_ = v___y_1083_;
v___y_1078_ = v___y_1084_;
v___y_1079_ = v_snd_1087_;
v___y_1080_ = v___x_1107_;
goto v___jp_1075_;
}
}
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_snd_1087_);
lean_dec(v_fst_1086_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v___y_1083_);
v___x_1108_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1108_;
}
}
v___jp_1109_:
{
if (lean_obj_tag(v_afterSep_x3f_1048_) == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1083_ = v___y_1110_;
v___y_1084_ = v___x_1111_;
goto v___jp_1082_;
}
else
{
lean_object* v_val_1112_; 
v_val_1112_ = lean_ctor_get(v_afterSep_x3f_1048_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v_afterSep_x3f_1048_, 1);
v___y_1083_ = v___y_1110_;
v___y_1084_ = v_val_1112_;
goto v___jp_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep___boxed(lean_object* v_sep_1115_, lean_object* v_sepArray_1116_, lean_object* v_afterElem_x3f_1117_, lean_object* v_afterSep_x3f_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_1115_, v_sepArray_1116_, v_afterElem_x3f_1117_, v_afterSep_x3f_1118_);
lean_dec_ref(v_sepArray_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0(lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v_inst_1122_, lean_object* v_R_1123_, lean_object* v_a_1124_, lean_object* v_b_1125_, lean_object* v_c_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep_spec__0___redArg(v___y_1120_, v___y_1121_, v_a_1124_, v_b_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep_spec__0___redArg(lean_object* v___y_1128_, lean_object* v_a_1129_, lean_object* v_b_1130_){
_start:
{
lean_object* v_array_1131_; lean_object* v_start_1132_; lean_object* v_stop_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1214_; 
v_array_1131_ = lean_ctor_get(v_a_1129_, 0);
v_start_1132_ = lean_ctor_get(v_a_1129_, 1);
v_stop_1133_ = lean_ctor_get(v_a_1129_, 2);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1129_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1135_ = v_a_1129_;
v_isShared_1136_ = v_isSharedCheck_1214_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_stop_1133_);
lean_inc(v_start_1132_);
lean_inc(v_array_1131_);
lean_dec(v_a_1129_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1214_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_nat_dec_lt(v_start_1132_, v_stop_1133_);
if (v___x_1137_ == 0)
{
lean_del_object(v___x_1135_);
lean_dec(v_stop_1133_);
lean_dec(v_start_1132_);
lean_dec_ref(v_array_1131_);
lean_dec_ref(v___y_1128_);
return v_b_1130_;
}
else
{
lean_object* v_snd_1138_; lean_object* v_snd_1139_; lean_object* v_fst_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1212_; 
v_snd_1138_ = lean_ctor_get(v_b_1130_, 1);
lean_inc(v_snd_1138_);
v_snd_1139_ = lean_ctor_get(v_snd_1138_, 1);
lean_inc(v_snd_1139_);
v_fst_1140_ = lean_ctor_get(v_b_1130_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_b_1130_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_b_1130_, 1);
lean_dec(v_unused_1213_);
v___x_1142_ = v_b_1130_;
v_isShared_1143_ = v_isSharedCheck_1212_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_fst_1140_);
lean_dec(v_b_1130_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1212_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_fst_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1210_; 
v_fst_1144_ = lean_ctor_get(v_snd_1138_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_snd_1138_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v_snd_1138_, 1);
lean_dec(v_unused_1211_);
v___x_1146_ = v_snd_1138_;
v_isShared_1147_ = v_isSharedCheck_1210_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_fst_1144_);
lean_dec(v_snd_1138_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1210_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_array_1148_; lean_object* v_start_1149_; lean_object* v_stop_1150_; uint8_t v___x_1151_; 
v_array_1148_ = lean_ctor_get(v_snd_1139_, 0);
v_start_1149_ = lean_ctor_get(v_snd_1139_, 1);
v_stop_1150_ = lean_ctor_get(v_snd_1139_, 2);
v___x_1151_ = lean_nat_dec_lt(v_start_1149_, v_stop_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1153_; 
lean_del_object(v___x_1135_);
lean_dec(v_stop_1133_);
lean_dec(v_start_1132_);
lean_dec_ref(v_array_1131_);
lean_dec_ref(v___y_1128_);
if (v_isShared_1147_ == 0)
{
v___x_1153_ = v___x_1146_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_fst_1144_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_snd_1139_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1153_);
v___x_1155_ = v___x_1142_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1206_; 
lean_inc(v_stop_1150_);
lean_inc(v_start_1149_);
lean_inc_ref(v_array_1148_);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_snd_1139_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; lean_object* v_unused_1209_; 
v_unused_1207_ = lean_ctor_get(v_snd_1139_, 2);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_snd_1139_, 1);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_snd_1139_, 0);
lean_dec(v_unused_1209_);
v___x_1159_ = v_snd_1139_;
v_isShared_1160_ = v_isSharedCheck_1206_;
goto v_resetjp_1158_;
}
else
{
lean_dec(v_snd_1139_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1206_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1161_ = lean_unsigned_to_nat(1u);
v___x_1162_ = lean_nat_add(v_start_1132_, v___x_1161_);
lean_inc_ref(v_array_1131_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 2, v_stop_1133_);
lean_ctor_set(v___x_1159_, 1, v___x_1162_);
lean_ctor_set(v___x_1159_, 0, v_array_1131_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_array_1131_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_stop_1133_);
v___x_1164_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1165_ = lean_array_fget(v_array_1131_, v_start_1132_);
lean_dec(v_start_1132_);
lean_dec_ref(v_array_1131_);
v___x_1166_ = lean_array_fget(v_array_1148_, v_start_1149_);
v___x_1167_ = lean_nat_add(v_start_1149_, v___x_1161_);
lean_dec(v_start_1149_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 2, v_stop_1150_);
lean_ctor_set(v___x_1135_, 1, v___x_1167_);
lean_ctor_set(v___x_1135_, 0, v_array_1148_);
v___x_1169_ = v___x_1135_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_array_1148_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_stop_1150_);
v___x_1169_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1170_ = lean_unsigned_to_nat(2u);
v___x_1171_ = lean_mk_empty_array_with_capacity(v___x_1170_);
lean_inc(v_fst_1140_);
lean_inc_ref(v___x_1171_);
v___x_1172_ = lean_array_push(v___x_1171_, v_fst_1140_);
v___x_1173_ = lean_array_push(v___x_1172_, v_fst_1144_);
v___x_1174_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1173_);
v___x_1175_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc(v___x_1165_);
v___x_1176_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1165_);
v___x_1177_ = lean_unsigned_to_nat(5u);
v___x_1178_ = lean_mk_empty_array_with_capacity(v___x_1177_);
lean_inc_ref(v___x_1178_);
v___x_1179_ = lean_array_push(v___x_1178_, v_fst_1140_);
lean_inc_ref_n(v___y_1128_, 2);
v___x_1180_ = lean_array_push(v___x_1179_, v___y_1128_);
lean_inc(v___x_1166_);
v___x_1181_ = lean_array_push(v___x_1180_, v___x_1166_);
v___x_1182_ = lean_array_push(v___x_1181_, v___x_1175_);
lean_inc_ref(v___x_1176_);
v___x_1183_ = lean_array_push(v___x_1182_, v___x_1176_);
v___x_1184_ = l_Lean_Fmt_TaggedDoc_join(v___x_1183_);
v___x_1185_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1186_ = lean_array_push(v___x_1178_, v___x_1174_);
v___x_1187_ = lean_array_push(v___x_1186_, v___y_1128_);
v___x_1188_ = lean_array_push(v___x_1187_, v___x_1166_);
v___x_1189_ = lean_array_push(v___x_1188_, v___x_1185_);
lean_inc_ref(v___x_1189_);
v___x_1190_ = lean_array_push(v___x_1189_, v___x_1176_);
v___x_1191_ = l_Lean_Fmt_TaggedDoc_join(v___x_1190_);
v___x_1192_ = lean_array_push(v___x_1171_, v___x_1184_);
v___x_1193_ = lean_array_push(v___x_1192_, v___x_1191_);
v___x_1194_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1193_);
v___x_1195_ = lean_array_push(v___x_1189_, v___x_1165_);
v___x_1196_ = l_Lean_Fmt_TaggedDoc_join(v___x_1195_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v___x_1169_);
lean_ctor_set(v___x_1146_, 0, v___x_1196_);
v___x_1198_ = v___x_1146_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1169_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1200_; 
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v___x_1198_);
lean_ctor_set(v___x_1142_, 0, v___x_1194_);
v___x_1200_ = v___x_1142_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
v_a_1129_ = v___x_1164_;
v_b_1130_ = v___x_1200_;
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(lean_object* v_sep_1215_, lean_object* v_sepArray_1216_, lean_object* v_afterElem_x3f_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v_elems_1222_; lean_object* v_seps_1223_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1250_; 
v___x_1218_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (lean_obj_tag(v_afterElem_x3f_1217_) == 0)
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1250_ = v___x_1275_;
goto v___jp_1249_;
}
else
{
lean_object* v_val_1276_; 
v_val_1276_ = lean_ctor_get(v_afterElem_x3f_1217_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v_afterElem_x3f_1217_, 1);
v___y_1250_ = v_val_1276_;
goto v___jp_1249_;
}
v___jp_1219_:
{
lean_object* v_lastNotFlattened_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v_lastNotFlattened_1224_ = lean_array_get(v___x_1218_, v_elems_1222_, v___y_1220_);
v___x_1225_ = lean_array_get_size(v_elems_1222_);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_dec_eq(v___x_1225_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_object* v_lastFlattened_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_snd_1235_; lean_object* v_fst_1236_; lean_object* v_fst_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_inc(v_lastNotFlattened_1224_);
v_lastFlattened_1228_ = l_Lean_Fmt_TaggedDoc_flattened(v_lastNotFlattened_1224_);
v___x_1229_ = lean_array_get_size(v_seps_1223_);
v___x_1230_ = l_Array_toSubarray___redArg(v_seps_1223_, v___y_1220_, v___x_1229_);
v___x_1231_ = l_Array_toSubarray___redArg(v_elems_1222_, v___x_1226_, v___x_1225_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_lastNotFlattened_1224_);
lean_ctor_set(v___x_1232_, 1, v___x_1230_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_lastFlattened_1228_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep_spec__0___redArg(v___y_1221_, v___x_1231_, v___x_1233_);
v_snd_1235_ = lean_ctor_get(v___x_1234_, 1);
lean_inc(v_snd_1235_);
v_fst_1236_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_fst_1236_);
lean_dec_ref(v___x_1234_);
v_fst_1237_ = lean_ctor_get(v_snd_1235_, 0);
lean_inc(v_fst_1237_);
lean_dec(v_snd_1235_);
v___x_1238_ = lean_unsigned_to_nat(2u);
v___x_1239_ = lean_mk_empty_array_with_capacity(v___x_1238_);
v___x_1240_ = lean_array_push(v___x_1239_, v_fst_1236_);
v___x_1241_ = lean_array_push(v___x_1240_, v_fst_1237_);
v___x_1242_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1241_);
return v___x_1242_;
}
else
{
lean_dec_ref(v_seps_1223_);
lean_dec_ref(v_elems_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
return v_lastNotFlattened_1224_;
}
}
v___jp_1243_:
{
lean_object* v_seps_1248_; 
v_seps_1248_ = lean_array_pop(v___y_1244_);
v___y_1220_ = v___y_1245_;
v___y_1221_ = v___y_1246_;
v_elems_1222_ = v___y_1247_;
v_seps_1223_ = v_seps_1248_;
goto v___jp_1219_;
}
v___jp_1249_:
{
lean_object* v___x_1251_; lean_object* v_fst_1252_; lean_object* v_snd_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1251_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_split(v_sep_1215_, v_sepArray_1216_);
v_fst_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_fst_1252_);
v_snd_1253_ = lean_ctor_get(v___x_1251_, 1);
lean_inc(v_snd_1253_);
lean_dec_ref(v___x_1251_);
v___x_1254_ = lean_array_get_size(v_fst_1252_);
v___x_1255_ = lean_unsigned_to_nat(0u);
v___x_1256_ = lean_nat_dec_eq(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1257_ = lean_array_get_size(v_snd_1253_);
v___x_1258_ = lean_nat_dec_eq(v___x_1257_, v___x_1254_);
if (v___x_1258_ == 0)
{
v___y_1220_ = v___x_1255_;
v___y_1221_ = v___y_1250_;
v_elems_1222_ = v_fst_1252_;
v_seps_1223_ = v_snd_1253_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_sub(v___x_1254_, v___x_1259_);
v___x_1261_ = lean_nat_dec_lt(v___x_1260_, v___x_1254_);
if (v___x_1261_ == 0)
{
lean_dec(v___x_1260_);
v___y_1244_ = v_snd_1253_;
v___y_1245_ = v___x_1255_;
v___y_1246_ = v___y_1250_;
v___y_1247_ = v_fst_1252_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1262_; lean_object* v_trailingSep_1263_; lean_object* v_v_1264_; lean_object* v___x_1265_; lean_object* v_xs_x27_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1262_ = lean_nat_sub(v___x_1257_, v___x_1259_);
v_trailingSep_1263_ = lean_array_get_borrowed(v___x_1218_, v_snd_1253_, v___x_1262_);
lean_dec(v___x_1262_);
v_v_1264_ = lean_array_fget(v_fst_1252_, v___x_1260_);
v___x_1265_ = lean_box(0);
v_xs_x27_1266_ = lean_array_fset(v_fst_1252_, v___x_1260_, v___x_1265_);
v___x_1267_ = lean_unsigned_to_nat(3u);
v___x_1268_ = lean_mk_empty_array_with_capacity(v___x_1267_);
v___x_1269_ = lean_array_push(v___x_1268_, v_v_1264_);
lean_inc_ref(v___y_1250_);
v___x_1270_ = lean_array_push(v___x_1269_, v___y_1250_);
lean_inc(v_trailingSep_1263_);
v___x_1271_ = lean_array_push(v___x_1270_, v_trailingSep_1263_);
v___x_1272_ = l_Lean_Fmt_TaggedDoc_join(v___x_1271_);
v___x_1273_ = lean_array_fset(v_xs_x27_1266_, v___x_1260_, v___x_1272_);
lean_dec(v___x_1260_);
v___y_1244_ = v_snd_1253_;
v___y_1245_ = v___x_1255_;
v___y_1246_ = v___y_1250_;
v___y_1247_ = v___x_1273_;
goto v___jp_1243_;
}
}
}
else
{
lean_object* v___x_1274_; 
lean_dec(v_snd_1253_);
lean_dec(v_fst_1252_);
lean_dec_ref(v___y_1250_);
v___x_1274_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1274_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep___boxed(lean_object* v_sep_1277_, lean_object* v_sepArray_1278_, lean_object* v_afterElem_x3f_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(v_sep_1277_, v_sepArray_1278_, v_afterElem_x3f_1279_);
lean_dec_ref(v_sepArray_1278_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep_spec__0(lean_object* v___y_1281_, lean_object* v_inst_1282_, lean_object* v_R_1283_, lean_object* v_a_1284_, lean_object* v_b_1285_, lean_object* v_c_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep_spec__0___redArg(v___y_1281_, v_a_1284_, v_b_1285_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepArray___closed__0(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = l_Lean_Fmt_TaggedDoc_space;
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray(lean_object* v_sep_1290_, lean_object* v_sepArray_1291_, lean_object* v_format_1292_){
_start:
{
lean_object* v___x_1293_; uint8_t v___y_1295_; 
v___x_1293_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
switch(lean_obj_tag(v_format_1292_))
{
case 1:
{
uint8_t v_trailingSep_1323_; 
v_trailingSep_1323_ = lean_ctor_get_uint8(v_format_1292_, sizeof(void*)*1 + 1);
v___y_1295_ = v_trailingSep_1323_;
goto v___jp_1294_;
}
case 3:
{
uint8_t v_trailingSep_1324_; 
v_trailingSep_1324_ = lean_ctor_get_uint8(v_format_1292_, sizeof(void*)*1);
v___y_1295_ = v_trailingSep_1324_;
goto v___jp_1294_;
}
default: 
{
uint8_t v_trailingSep_1325_; 
v_trailingSep_1325_ = lean_ctor_get_uint8(v_format_1292_, sizeof(void*)*2);
v___y_1295_ = v_trailingSep_1325_;
goto v___jp_1294_;
}
}
v___jp_1294_:
{
lean_object* v_sepArray_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
lean_inc_ref(v_sep_1290_);
v_sepArray_1296_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1290_, v_sepArray_1291_, v___y_1295_);
v___x_1297_ = lean_array_get_size(v_sepArray_1296_);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_nat_dec_eq(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_dec_eq(v___x_1297_, v___x_1300_);
if (v___x_1301_ == 0)
{
switch(lean_obj_tag(v_format_1292_))
{
case 0:
{
lean_object* v_afterElem_x3f_1302_; lean_object* v_afterSep_x3f_1303_; lean_object* v___x_1304_; 
v_afterElem_x3f_1302_ = lean_ctor_get(v_format_1292_, 0);
lean_inc(v_afterElem_x3f_1302_);
v_afterSep_x3f_1303_ = lean_ctor_get(v_format_1292_, 1);
lean_inc(v_afterSep_x3f_1303_);
lean_dec_ref_known(v_format_1292_, 2);
v___x_1304_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1290_, v_sepArray_1296_, v_afterElem_x3f_1302_, v_afterSep_x3f_1303_);
return v___x_1304_;
}
case 1:
{
uint8_t v_allowFlattening_1305_; lean_object* v_afterElem_x3f_1306_; lean_object* v_joinedUsingNl_1307_; 
v_allowFlattening_1305_ = lean_ctor_get_uint8(v_format_1292_, sizeof(void*)*1);
v_afterElem_x3f_1306_ = lean_ctor_get(v_format_1292_, 0);
lean_inc_n(v_afterElem_x3f_1306_, 2);
lean_dec_ref_known(v_format_1292_, 1);
lean_inc_ref(v_sep_1290_);
v_joinedUsingNl_1307_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingNl(v_sep_1290_, v_sepArray_1296_, v_afterElem_x3f_1306_);
if (v_allowFlattening_1305_ == 0)
{
lean_dec(v_afterElem_x3f_1306_);
lean_dec_ref(v_sepArray_1296_);
lean_dec_ref(v_sep_1290_);
return v_joinedUsingNl_1307_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1308_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepArray___closed__0, &l_Lean_Fmt_Layouts_sepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_sepArray___closed__0);
v___x_1309_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_joinUsingSep(v_sep_1290_, v_sepArray_1296_, v_afterElem_x3f_1306_, v___x_1308_);
v___x_1310_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_1309_);
v___x_1311_ = lean_unsigned_to_nat(2u);
v___x_1312_ = lean_mk_empty_array_with_capacity(v___x_1311_);
v___x_1313_ = lean_array_push(v___x_1312_, v___x_1310_);
v___x_1314_ = lean_array_push(v___x_1313_, v_joinedUsingNl_1307_);
v___x_1315_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_1314_);
return v___x_1315_;
}
}
case 2:
{
lean_object* v_afterElem_x3f_1316_; lean_object* v_afterSep_x3f_1317_; lean_object* v___x_1318_; 
v_afterElem_x3f_1316_ = lean_ctor_get(v_format_1292_, 0);
lean_inc(v_afterElem_x3f_1316_);
v_afterSep_x3f_1317_ = lean_ctor_get(v_format_1292_, 1);
lean_inc(v_afterSep_x3f_1317_);
lean_dec_ref_known(v_format_1292_, 2);
v___x_1318_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSep(v_sep_1290_, v_sepArray_1296_, v_afterElem_x3f_1316_, v_afterSep_x3f_1317_);
lean_dec_ref(v_sepArray_1296_);
return v___x_1318_;
}
default: 
{
lean_object* v_afterElem_x3f_1319_; lean_object* v___x_1320_; 
v_afterElem_x3f_1319_ = lean_ctor_get(v_format_1292_, 0);
lean_inc(v_afterElem_x3f_1319_);
lean_dec_ref_known(v_format_1292_, 1);
v___x_1320_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_fillUsingSpacedSep(v_sep_1290_, v_sepArray_1296_, v_afterElem_x3f_1319_);
lean_dec_ref(v_sepArray_1296_);
return v___x_1320_;
}
}
}
else
{
lean_object* v___x_1321_; 
lean_dec_ref(v_format_1292_);
lean_dec_ref(v_sep_1290_);
v___x_1321_ = lean_array_get(v___x_1293_, v_sepArray_1296_, v___x_1298_);
lean_dec_ref(v_sepArray_1296_);
return v___x_1321_;
}
}
else
{
lean_object* v___x_1322_; 
lean_dec_ref(v_sepArray_1296_);
lean_dec_ref(v_format_1292_);
lean_dec_ref(v_sep_1290_);
v___x_1322_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepArray___boxed(lean_object* v_sep_1326_, lean_object* v_sepArray_1327_, lean_object* v_format_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1326_, v_sepArray_1327_, v_format_1328_);
lean_dec_ref(v_sepArray_1327_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__0(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepLines___closed__1(void){
_start:
{
uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = 1;
v___x_1333_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__0, &l_Lean_Fmt_Layouts_sepLines___closed__0_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__0);
v___x_1334_ = lean_box(0);
v___x_1335_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*2, v___x_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines(lean_object* v_sep_1336_, lean_object* v_lines_1337_, uint8_t v_includeSeps_1338_){
_start:
{
if (v_includeSeps_1338_ == 0)
{
lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = 1;
v___x_1341_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*1, v_includeSeps_1338_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*1 + 1, v___x_1340_);
v___x_1342_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1336_, v_lines_1337_, v___x_1341_);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepLines___closed__1, &l_Lean_Fmt_Layouts_sepLines___closed__1_once, _init_l_Lean_Fmt_Layouts_sepLines___closed__1);
v___x_1344_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1336_, v_lines_1337_, v___x_1343_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepLines___boxed(lean_object* v_sep_1345_, lean_object* v_lines_1346_, lean_object* v_includeSeps_1347_){
_start:
{
uint8_t v_includeSeps_boxed_1348_; lean_object* v_res_1349_; 
v_includeSeps_boxed_1348_ = lean_unbox(v_includeSeps_1347_);
v_res_1349_ = l_Lean_Fmt_Layouts_sepLines(v_sep_1345_, v_lines_1346_, v_includeSeps_boxed_1348_);
lean_dec_ref(v_lines_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill(lean_object* v_sep_1353_, lean_object* v_elems_1354_){
_start:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = ((lean_object*)(l_Lean_Fmt_Layouts_sepFill___closed__0));
v___x_1356_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1353_, v_elems_1354_, v___x_1355_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepFill___boxed(lean_object* v_sep_1357_, lean_object* v_elems_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Fmt_Layouts_sepFill(v_sep_1357_, v_elems_1358_);
lean_dec_ref(v_elems_1358_);
return v_res_1359_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2(void){
_start:
{
uint8_t v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1366_ = 1;
v___x_1367_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__1);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
lean_ctor_set(v___x_1369_, 1, v___x_1367_);
lean_ctor_set_uint8(v___x_1369_, sizeof(void*)*2, v___x_1366_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical(lean_object* v_sep_1370_, lean_object* v_elems_1371_, uint8_t v_includeSeps_1372_){
_start:
{
uint8_t v___x_1373_; lean_object* v_elems_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1373_ = 1;
lean_inc_ref(v_sep_1370_);
v_elems_1374_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_1370_, v_elems_1371_, v___x_1373_);
v___x_1375_ = lean_array_get_size(v_elems_1374_);
v___x_1376_ = lean_unsigned_to_nat(1u);
v___x_1377_ = lean_nat_dec_eq(v___x_1375_, v___x_1376_);
if (v___x_1377_ == 0)
{
if (v_includeSeps_1372_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__0));
v___x_1379_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1370_, v_elems_1374_, v___x_1378_);
lean_dec_ref(v_elems_1374_);
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v___x_1381_ = l_Lean_Fmt_Layouts_sepArray(v_sep_1370_, v_elems_1374_, v___x_1380_);
lean_dec_ref(v_elems_1374_);
v___x_1382_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_1381_);
return v___x_1382_;
}
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v_sep_1370_);
v___x_1383_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = lean_array_get(v___x_1383_, v_elems_1374_, v___x_1384_);
lean_dec_ref(v_elems_1374_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_sepHorizontalOrVertical___boxed(lean_object* v_sep_1386_, lean_object* v_elems_1387_, lean_object* v_includeSeps_1388_){
_start:
{
uint8_t v_includeSeps_boxed_1389_; lean_object* v_res_1390_; 
v_includeSeps_boxed_1389_ = lean_unbox(v_includeSeps_1388_);
v_res_1390_ = l_Lean_Fmt_Layouts_sepHorizontalOrVertical(v_sep_1386_, v_elems_1387_, v_includeSeps_boxed_1389_);
lean_dec_ref(v_elems_1387_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(lean_object* v___x_1391_, lean_object* v_docsWithIntermediateWhitespace_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v_fst_1394_; lean_object* v_snd_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1424_; 
v_fst_1394_ = lean_ctor_get(v_a_1393_, 0);
v_snd_1395_ = lean_ctor_get(v_a_1393_, 1);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_a_1393_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1397_ = v_a_1393_;
v_isShared_1398_ = v_isSharedCheck_1424_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_snd_1395_);
lean_inc(v_fst_1394_);
lean_dec(v_a_1393_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1424_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_lt(v_snd_1395_, v___x_1391_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1401_; 
if (v_isShared_1398_ == 0)
{
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_fst_1394_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_snd_1395_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___y_1408_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___f_1403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__0));
v___x_1404_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1405_ = lean_unsigned_to_nat(1u);
v___x_1406_ = lean_array_get_borrowed(v___x_1404_, v_docsWithIntermediateWhitespace_1392_, v_snd_1395_);
v___x_1419_ = lean_nat_add(v_snd_1395_, v___x_1405_);
v___x_1420_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1392_);
v___x_1421_ = lean_nat_dec_lt(v___x_1419_, v___x_1420_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
lean_dec(v___x_1419_);
v___x_1422_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_1408_ = v___x_1422_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_array_fget_borrowed(v_docsWithIntermediateWhitespace_1392_, v___x_1419_);
lean_dec(v___x_1419_);
lean_inc(v___x_1423_);
v___y_1408_ = v___x_1423_;
goto v___jp_1407_;
}
v___jp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_inc(v___x_1406_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1406_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___y_1408_);
lean_ctor_set(v___x_1410_, 1, v___f_1403_);
v___x_1411_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_1409_, v___x_1410_);
v___x_1412_ = lean_array_push(v_fst_1394_, v___x_1411_);
v___x_1413_ = lean_unsigned_to_nat(2u);
v___x_1414_ = lean_nat_add(v_snd_1395_, v___x_1413_);
lean_dec(v_snd_1395_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1414_);
lean_ctor_set(v___x_1397_, 0, v___x_1412_);
v___x_1416_ = v___x_1397_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
v_a_1393_ = v___x_1416_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg___boxed(lean_object* v___x_1425_, lean_object* v_docsWithIntermediateWhitespace_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1425_, v_docsWithIntermediateWhitespace_1426_, v_a_1427_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1426_);
lean_dec(v___x_1425_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace(lean_object* v_docsWithIntermediateWhitespace_1434_){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_array_get_size(v_docsWithIntermediateWhitespace_1434_);
v___x_1436_ = lean_unsigned_to_nat(0u);
v___x_1437_ = lean_nat_dec_eq(v___x_1435_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = lean_unsigned_to_nat(1u);
v___x_1439_ = lean_nat_dec_eq(v___x_1435_, v___x_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v_fst_1442_; lean_object* v___x_1443_; 
v___x_1440_ = ((lean_object*)(l_Lean_Fmt_Layouts_retainedWhitespace___closed__1));
v___x_1441_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1435_, v_docsWithIntermediateWhitespace_1434_, v___x_1440_);
v_fst_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_fst_1442_);
lean_dec_ref(v___x_1441_);
v___x_1443_ = l_Lean_Fmt_TaggedDoc_combine(v_fst_1442_);
lean_dec(v_fst_1442_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_1445_ = lean_array_get_borrowed(v___x_1444_, v_docsWithIntermediateWhitespace_1434_, v___x_1436_);
lean_inc(v___x_1445_);
return v___x_1445_;
}
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_retainedWhitespace___boxed(lean_object* v_docsWithIntermediateWhitespace_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_Fmt_Layouts_retainedWhitespace(v_docsWithIntermediateWhitespace_1447_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1447_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(lean_object* v___x_1449_, lean_object* v_docsWithIntermediateWhitespace_1450_, lean_object* v_inst_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___redArg(v___x_1449_, v_docsWithIntermediateWhitespace_1450_, v_a_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0___boxed(lean_object* v___x_1454_, lean_object* v_docsWithIntermediateWhitespace_1455_, lean_object* v_inst_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Fmt_Layouts_retainedWhitespace_spec__0(v___x_1454_, v_docsWithIntermediateWhitespace_1455_, v_inst_1456_, v_a_1457_);
lean_dec_ref(v_docsWithIntermediateWhitespace_1455_);
lean_dec(v___x_1454_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1___redArg(lean_object* v_v_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_unsafe__1(lean_object* v_00_u03c4_1461_, lean_object* v_v_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(lean_object* v_a_1464_, lean_object* v_x_1465_){
_start:
{
if (lean_obj_tag(v_x_1465_) == 0)
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_box(0);
return v___x_1466_;
}
else
{
lean_object* v_key_1467_; lean_object* v_value_1468_; lean_object* v_tail_1469_; size_t v_ptr_1470_; size_t v_ptr_1471_; uint8_t v___x_1472_; 
v_key_1467_ = lean_ctor_get(v_x_1465_, 0);
v_value_1468_ = lean_ctor_get(v_x_1465_, 1);
v_tail_1469_ = lean_ctor_get(v_x_1465_, 2);
v_ptr_1470_ = lean_ctor_get_usize(v_key_1467_, 1);
v_ptr_1471_ = lean_ctor_get_usize(v_a_1464_, 1);
v___x_1472_ = lean_usize_dec_eq(v_ptr_1470_, v_ptr_1471_);
if (v___x_1472_ == 0)
{
v_x_1465_ = v_tail_1469_;
goto _start;
}
else
{
lean_object* v___x_1474_; 
lean_inc(v_value_1468_);
v___x_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_value_1468_);
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg___boxed(lean_object* v_a_1475_, lean_object* v_x_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1475_, v_x_1476_);
lean_dec(v_x_1476_);
lean_dec_ref(v_a_1475_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(lean_object* v_m_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v_buckets_1480_; size_t v_ptr_1481_; lean_object* v___x_1482_; uint64_t v___x_1483_; uint64_t v___x_1484_; uint64_t v___x_1485_; uint64_t v_fold_1486_; uint64_t v___x_1487_; uint64_t v___x_1488_; uint64_t v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; size_t v___x_1492_; size_t v___x_1493_; size_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_buckets_1480_ = lean_ctor_get(v_m_1478_, 1);
v_ptr_1481_ = lean_ctor_get_usize(v_a_1479_, 1);
v___x_1482_ = lean_array_get_size(v_buckets_1480_);
v___x_1483_ = lean_usize_to_uint64(v_ptr_1481_);
v___x_1484_ = 32ULL;
v___x_1485_ = lean_uint64_shift_right(v___x_1483_, v___x_1484_);
v_fold_1486_ = lean_uint64_xor(v___x_1483_, v___x_1485_);
v___x_1487_ = 16ULL;
v___x_1488_ = lean_uint64_shift_right(v_fold_1486_, v___x_1487_);
v___x_1489_ = lean_uint64_xor(v_fold_1486_, v___x_1488_);
v___x_1490_ = lean_uint64_to_usize(v___x_1489_);
v___x_1491_ = lean_usize_of_nat(v___x_1482_);
v___x_1492_ = ((size_t)1ULL);
v___x_1493_ = lean_usize_sub(v___x_1491_, v___x_1492_);
v___x_1494_ = lean_usize_land(v___x_1490_, v___x_1493_);
v___x_1495_ = lean_array_uget_borrowed(v_buckets_1480_, v___x_1494_);
v___x_1496_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1479_, v___x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg___boxed(lean_object* v_m_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1497_, v_a_1498_);
lean_dec_ref(v_a_1498_);
lean_dec_ref(v_m_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(lean_object* v_a_1500_, lean_object* v_b_1501_, lean_object* v_x_1502_){
_start:
{
if (lean_obj_tag(v_x_1502_) == 0)
{
lean_dec(v_b_1501_);
lean_dec_ref(v_a_1500_);
return v_x_1502_;
}
else
{
lean_object* v_key_1503_; lean_object* v_value_1504_; lean_object* v_tail_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1519_; 
v_key_1503_ = lean_ctor_get(v_x_1502_, 0);
v_value_1504_ = lean_ctor_get(v_x_1502_, 1);
v_tail_1505_ = lean_ctor_get(v_x_1502_, 2);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_x_1502_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1507_ = v_x_1502_;
v_isShared_1508_ = v_isSharedCheck_1519_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_tail_1505_);
lean_inc(v_value_1504_);
lean_inc(v_key_1503_);
lean_dec(v_x_1502_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1519_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
size_t v_ptr_1509_; size_t v_ptr_1510_; uint8_t v___x_1511_; 
v_ptr_1509_ = lean_ctor_get_usize(v_key_1503_, 1);
v_ptr_1510_ = lean_ctor_get_usize(v_a_1500_, 1);
v___x_1511_ = lean_usize_dec_eq(v_ptr_1509_, v_ptr_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1500_, v_b_1501_, v_tail_1505_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 2, v___x_1512_);
v___x_1514_ = v___x_1507_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_key_1503_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_value_1504_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
else
{
lean_object* v___x_1517_; 
lean_dec(v_value_1504_);
lean_dec(v_key_1503_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v_b_1501_);
lean_ctor_set(v___x_1507_, 0, v_a_1500_);
v___x_1517_ = v___x_1507_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1500_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_b_1501_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_tail_1505_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
return v_x_1520_;
}
else
{
lean_object* v_key_1522_; lean_object* v_value_1523_; lean_object* v_tail_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1548_; 
v_key_1522_ = lean_ctor_get(v_x_1521_, 0);
v_value_1523_ = lean_ctor_get(v_x_1521_, 1);
v_tail_1524_ = lean_ctor_get(v_x_1521_, 2);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1526_ = v_x_1521_;
v_isShared_1527_ = v_isSharedCheck_1548_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_tail_1524_);
lean_inc(v_value_1523_);
lean_inc(v_key_1522_);
lean_dec(v_x_1521_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1548_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
size_t v_ptr_1528_; lean_object* v___x_1529_; uint64_t v___x_1530_; uint64_t v___x_1531_; uint64_t v___x_1532_; uint64_t v_fold_1533_; uint64_t v___x_1534_; uint64_t v___x_1535_; uint64_t v___x_1536_; size_t v___x_1537_; size_t v___x_1538_; size_t v___x_1539_; size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v_ptr_1528_ = lean_ctor_get_usize(v_key_1522_, 1);
v___x_1529_ = lean_array_get_size(v_x_1520_);
v___x_1530_ = lean_usize_to_uint64(v_ptr_1528_);
v___x_1531_ = 32ULL;
v___x_1532_ = lean_uint64_shift_right(v___x_1530_, v___x_1531_);
v_fold_1533_ = lean_uint64_xor(v___x_1530_, v___x_1532_);
v___x_1534_ = 16ULL;
v___x_1535_ = lean_uint64_shift_right(v_fold_1533_, v___x_1534_);
v___x_1536_ = lean_uint64_xor(v_fold_1533_, v___x_1535_);
v___x_1537_ = lean_uint64_to_usize(v___x_1536_);
v___x_1538_ = lean_usize_of_nat(v___x_1529_);
v___x_1539_ = ((size_t)1ULL);
v___x_1540_ = lean_usize_sub(v___x_1538_, v___x_1539_);
v___x_1541_ = lean_usize_land(v___x_1537_, v___x_1540_);
v___x_1542_ = lean_array_uget_borrowed(v_x_1520_, v___x_1541_);
lean_inc(v___x_1542_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 2, v___x_1542_);
v___x_1544_ = v___x_1526_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_key_1522_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_value_1523_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_array_uset(v_x_1520_, v___x_1541_, v___x_1544_);
v_x_1520_ = v___x_1545_;
v_x_1521_ = v_tail_1524_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(lean_object* v_i_1549_, lean_object* v_source_1550_, lean_object* v_target_1551_){
_start:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_array_get_size(v_source_1550_);
v___x_1553_ = lean_nat_dec_lt(v_i_1549_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_dec_ref(v_source_1550_);
lean_dec(v_i_1549_);
return v_target_1551_;
}
else
{
lean_object* v_es_1554_; lean_object* v___x_1555_; lean_object* v_source_1556_; lean_object* v_target_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_es_1554_ = lean_array_fget(v_source_1550_, v_i_1549_);
v___x_1555_ = lean_box(0);
v_source_1556_ = lean_array_fset(v_source_1550_, v_i_1549_, v___x_1555_);
v_target_1557_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_target_1551_, v_es_1554_);
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_nat_add(v_i_1549_, v___x_1558_);
lean_dec(v_i_1549_);
v_i_1549_ = v___x_1559_;
v_source_1550_ = v_source_1556_;
v_target_1551_ = v_target_1557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(lean_object* v_data_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_nbuckets_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1562_ = lean_array_get_size(v_data_1561_);
v___x_1563_ = lean_unsigned_to_nat(2u);
v_nbuckets_1564_ = lean_nat_mul(v___x_1562_, v___x_1563_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_mk_array(v_nbuckets_1564_, v___x_1566_);
v___x_1568_ = lean_array_propagate_mark(v_data_1561_, v___x_1567_);
v___x_1569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v___x_1565_, v_data_1561_, v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(lean_object* v_a_1570_, lean_object* v_x_1571_){
_start:
{
if (lean_obj_tag(v_x_1571_) == 0)
{
uint8_t v___x_1572_; 
v___x_1572_ = 0;
return v___x_1572_;
}
else
{
lean_object* v_key_1573_; lean_object* v_tail_1574_; size_t v_ptr_1575_; size_t v_ptr_1576_; uint8_t v___x_1577_; 
v_key_1573_ = lean_ctor_get(v_x_1571_, 0);
v_tail_1574_ = lean_ctor_get(v_x_1571_, 2);
v_ptr_1575_ = lean_ctor_get_usize(v_key_1573_, 1);
v_ptr_1576_ = lean_ctor_get_usize(v_a_1570_, 1);
v___x_1577_ = lean_usize_dec_eq(v_ptr_1575_, v_ptr_1576_);
if (v___x_1577_ == 0)
{
v_x_1571_ = v_tail_1574_;
goto _start;
}
else
{
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg___boxed(lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_res_1581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1579_, v_x_1580_);
lean_dec(v_x_1580_);
lean_dec_ref(v_a_1579_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(lean_object* v_m_1583_, lean_object* v_a_1584_, lean_object* v_b_1585_){
_start:
{
lean_object* v_size_1586_; lean_object* v_buckets_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1631_; 
v_size_1586_ = lean_ctor_get(v_m_1583_, 0);
v_buckets_1587_ = lean_ctor_get(v_m_1583_, 1);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_m_1583_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1589_ = v_m_1583_;
v_isShared_1590_ = v_isSharedCheck_1631_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_buckets_1587_);
lean_inc(v_size_1586_);
lean_dec(v_m_1583_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1631_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
size_t v_ptr_1591_; lean_object* v___x_1592_; uint64_t v___x_1593_; uint64_t v___x_1594_; uint64_t v___x_1595_; uint64_t v_fold_1596_; uint64_t v___x_1597_; uint64_t v___x_1598_; uint64_t v___x_1599_; size_t v___x_1600_; size_t v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; lean_object* v_bkt_1605_; uint8_t v___x_1606_; 
v_ptr_1591_ = lean_ctor_get_usize(v_a_1584_, 1);
v___x_1592_ = lean_array_get_size(v_buckets_1587_);
v___x_1593_ = lean_usize_to_uint64(v_ptr_1591_);
v___x_1594_ = 32ULL;
v___x_1595_ = lean_uint64_shift_right(v___x_1593_, v___x_1594_);
v_fold_1596_ = lean_uint64_xor(v___x_1593_, v___x_1595_);
v___x_1597_ = 16ULL;
v___x_1598_ = lean_uint64_shift_right(v_fold_1596_, v___x_1597_);
v___x_1599_ = lean_uint64_xor(v_fold_1596_, v___x_1598_);
v___x_1600_ = lean_uint64_to_usize(v___x_1599_);
v___x_1601_ = lean_usize_of_nat(v___x_1592_);
v___x_1602_ = ((size_t)1ULL);
v___x_1603_ = lean_usize_sub(v___x_1601_, v___x_1602_);
v___x_1604_ = lean_usize_land(v___x_1600_, v___x_1603_);
v_bkt_1605_ = lean_array_uget_borrowed(v_buckets_1587_, v___x_1604_);
v___x_1606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1584_, v_bkt_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v_size_x27_1608_; lean_object* v___x_1609_; lean_object* v_buckets_x27_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v___x_1607_ = lean_unsigned_to_nat(1u);
v_size_x27_1608_ = lean_nat_add(v_size_1586_, v___x_1607_);
lean_dec(v_size_1586_);
lean_inc(v_bkt_1605_);
v___x_1609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1609_, 0, v_a_1584_);
lean_ctor_set(v___x_1609_, 1, v_b_1585_);
lean_ctor_set(v___x_1609_, 2, v_bkt_1605_);
v_buckets_x27_1610_ = lean_array_uset(v_buckets_1587_, v___x_1604_, v___x_1609_);
v___x_1611_ = lean_unsigned_to_nat(4u);
v___x_1612_ = lean_nat_mul(v_size_x27_1608_, v___x_1611_);
v___x_1613_ = lean_unsigned_to_nat(3u);
v___x_1614_ = lean_nat_div(v___x_1612_, v___x_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_array_get_size(v_buckets_x27_1610_);
v___x_1616_ = lean_nat_dec_le(v___x_1614_, v___x_1615_);
lean_dec(v___x_1614_);
if (v___x_1616_ == 0)
{
lean_object* v_val_1617_; lean_object* v___x_1619_; 
v_val_1617_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_buckets_x27_1610_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v_val_1617_);
lean_ctor_set(v___x_1589_, 0, v_size_x27_1608_);
v___x_1619_ = v___x_1589_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_size_x27_1608_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_val_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
else
{
lean_object* v___x_1622_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v_buckets_x27_1610_);
lean_ctor_set(v___x_1589_, 0, v_size_x27_1608_);
v___x_1622_ = v___x_1589_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_size_x27_1608_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_buckets_x27_1610_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_object* v___x_1624_; lean_object* v_buckets_x27_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_inc(v_bkt_1605_);
v___x_1624_ = lean_box(0);
v_buckets_x27_1625_ = lean_array_uset(v_buckets_1587_, v___x_1604_, v___x_1624_);
v___x_1626_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1584_, v_b_1585_, v_bkt_1605_);
v___x_1627_ = lean_array_uset(v_buckets_x27_1625_, v___x_1604_, v___x_1626_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v___x_1627_);
v___x_1629_ = v___x_1589_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_size_1586_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___y_1635_; 
switch(lean_obj_tag(v_a_1632_))
{
case 1:
{
lean_dec_ref_known(v_a_1632_, 2);
v___y_1635_ = v_a_1633_;
goto v___jp_1634_;
}
case 2:
{
lean_dec_ref_known(v_a_1632_, 2);
v___y_1635_ = v_a_1633_;
goto v___jp_1634_;
}
case 3:
{
lean_object* v_d_1639_; lean_object* v___x_1640_; 
v_d_1639_ = lean_ctor_get(v_a_1632_, 2);
lean_inc(v_d_1639_);
lean_dec_ref_known(v_a_1632_, 3);
v___x_1640_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1639_, v_a_1633_);
return v___x_1640_;
}
case 4:
{
lean_object* v_d_1641_; lean_object* v___x_1642_; 
v_d_1641_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_d_1641_);
lean_dec_ref_known(v_a_1632_, 2);
v___x_1642_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1641_, v_a_1633_);
return v___x_1642_;
}
case 5:
{
lean_object* v_d_1643_; lean_object* v___x_1644_; 
v_d_1643_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_d_1643_);
lean_dec_ref_known(v_a_1632_, 2);
v___x_1644_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1643_, v_a_1633_);
return v___x_1644_;
}
case 6:
{
lean_object* v_d_1645_; lean_object* v___x_1646_; 
v_d_1645_ = lean_ctor_get(v_a_1632_, 2);
lean_inc(v_d_1645_);
lean_dec_ref_known(v_a_1632_, 3);
v___x_1646_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1645_, v_a_1633_);
return v___x_1646_;
}
case 7:
{
uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec_ref_known(v_a_1632_, 2);
v___x_1647_ = 1;
v___x_1648_ = lean_box(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_a_1633_);
return v___x_1649_;
}
case 8:
{
lean_object* v_d_1650_; lean_object* v___x_1651_; 
v_d_1650_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_d_1650_);
lean_dec_ref_known(v_a_1632_, 2);
v___x_1651_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1650_, v_a_1633_);
return v___x_1651_;
}
case 9:
{
lean_object* v_d_1652_; lean_object* v___x_1653_; 
v_d_1652_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_d_1652_);
lean_dec_ref_known(v_a_1632_, 2);
v___x_1653_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1652_, v_a_1633_);
return v___x_1653_;
}
case 10:
{
lean_object* v_d_1654_; lean_object* v___x_1655_; 
v_d_1654_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_d_1654_);
lean_dec_ref_known(v_a_1632_, 2);
v___x_1655_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1654_, v_a_1633_);
return v___x_1655_;
}
case 11:
{
lean_object* v_d_1656_; lean_object* v___x_1657_; 
v_d_1656_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_d_1656_);
lean_dec_ref_known(v_a_1632_, 2);
v___x_1657_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1656_, v_a_1633_);
return v___x_1657_;
}
case 12:
{
lean_object* v_d_1658_; lean_object* v___x_1659_; 
v_d_1658_ = lean_ctor_get(v_a_1632_, 2);
lean_inc(v_d_1658_);
lean_dec_ref_known(v_a_1632_, 3);
v___x_1659_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1658_, v_a_1633_);
return v___x_1659_;
}
case 13:
{
lean_object* v_d_1660_; lean_object* v___x_1661_; 
v_d_1660_ = lean_ctor_get(v_a_1632_, 2);
lean_inc(v_d_1660_);
lean_dec_ref_known(v_a_1632_, 3);
v___x_1661_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1660_, v_a_1633_);
return v___x_1661_;
}
case 14:
{
lean_object* v_a_1662_; lean_object* v_b_1663_; lean_object* v___x_1664_; lean_object* v_fst_1665_; lean_object* v_snd_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_a_1662_ = lean_ctor_get(v_a_1632_, 1);
lean_inc(v_a_1662_);
v_b_1663_ = lean_ctor_get(v_a_1632_, 2);
lean_inc(v_b_1663_);
lean_dec_ref_known(v_a_1632_, 3);
v___x_1664_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_a_1662_, v_a_1633_);
v_fst_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_fst_1665_);
v_snd_1666_ = lean_ctor_get(v___x_1664_, 1);
lean_inc(v_snd_1666_);
lean_dec_ref(v___x_1664_);
v___x_1667_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_b_1663_, v_snd_1666_);
v___x_1668_ = lean_unbox(v_fst_1665_);
if (v___x_1668_ == 0)
{
lean_object* v_snd_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_snd_1669_ = lean_ctor_get(v___x_1667_, 1);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v___x_1667_, 0);
lean_dec(v_unused_1677_);
v___x_1671_ = v___x_1667_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_snd_1669_);
lean_dec(v___x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v_fst_1665_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_fst_1665_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_snd_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_dec(v_fst_1665_);
return v___x_1667_;
}
}
default: 
{
uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v_a_1632_);
v___x_1678_ = 0;
v___x_1679_ = lean_box(v___x_1678_);
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_a_1633_);
return v___x_1680_;
}
}
v___jp_1634_:
{
uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = 0;
v___x_1637_ = lean_box(v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___y_1635_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object* v_v_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_cacheKey_1683_; lean_object* v___x_1684_; 
lean_inc(v_v_1681_);
v_cacheKey_1683_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1681_);
v___x_1684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_a_1682_, v_cacheKey_1683_);
if (lean_obj_tag(v___x_1684_) == 1)
{
lean_object* v_val_1685_; lean_object* v___x_1686_; 
lean_dec_ref(v_cacheKey_1683_);
lean_dec(v_v_1681_);
v_val_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_val_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v___x_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_val_1685_);
lean_ctor_set(v___x_1686_, 1, v_a_1682_);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; lean_object* v_fst_1688_; lean_object* v_snd_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v___x_1684_);
v___x_1687_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_v_1681_, v_a_1682_);
v_fst_1688_ = lean_ctor_get(v___x_1687_, 0);
v_snd_1689_ = lean_ctor_get(v___x_1687_, 1);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1691_ = v___x_1687_;
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_snd_1689_);
lean_inc(v_fst_1688_);
lean_dec(v___x_1687_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_inc(v_fst_1688_);
v___x_1693_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_snd_1689_, v_cacheKey_1683_, v_fst_1688_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 1, v___x_1693_);
v___x_1695_ = v___x_1691_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_fst_1688_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object* v_00_u03c4_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_a_1699_, v_a_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object* v_00_u03c4_1702_, lean_object* v_v_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1703_, v_a_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object* v_00_u03c4_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_m_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1708_, v_a_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object* v_00_u03c4_1711_, lean_object* v_00_u03b2_1712_, lean_object* v_m_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(v_00_u03c4_1711_, v_00_u03b2_1712_, v_m_1713_, v_a_1714_);
lean_dec_ref(v_a_1714_);
lean_dec_ref(v_m_1713_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object* v_00_u03c4_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_m_1718_, lean_object* v_a_1719_, lean_object* v_b_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_m_1718_, v_a_1719_, v_b_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object* v_00_u03c4_1722_, lean_object* v_00_u03b2_1723_, lean_object* v_a_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1724_, v_x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object* v_00_u03c4_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_a_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(v_00_u03c4_1727_, v_00_u03b2_1728_, v_a_1729_, v_x_1730_);
lean_dec(v_x_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1731_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object* v_00_u03c4_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_a_1734_, lean_object* v_x_1735_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1734_, v_x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object* v_00_u03c4_1737_, lean_object* v_00_u03b2_1738_, lean_object* v_a_1739_, lean_object* v_x_1740_){
_start:
{
uint8_t v_res_1741_; lean_object* v_r_1742_; 
v_res_1741_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(v_00_u03c4_1737_, v_00_u03b2_1738_, v_a_1739_, v_x_1740_);
lean_dec(v_x_1740_);
lean_dec_ref(v_a_1739_);
v_r_1742_ = lean_box(v_res_1741_);
return v_r_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object* v_00_u03c4_1743_, lean_object* v_00_u03b2_1744_, lean_object* v_data_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_data_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object* v_00_u03c4_1747_, lean_object* v_00_u03b2_1748_, lean_object* v_a_1749_, lean_object* v_b_1750_, lean_object* v_x_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1749_, v_b_1750_, v_x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object* v_00_u03c4_1753_, lean_object* v_00_u03b2_1754_, lean_object* v_i_1755_, lean_object* v_source_1756_, lean_object* v_target_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v_i_1755_, v_source_1756_, v_target_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03c4_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_x_1761_, v_x_1762_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0(void){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_unsigned_to_nat(16u);
v___x_1766_ = lean_mk_array(v___x_1765_, v___x_1764_);
return v___x_1766_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0);
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(lean_object* v_v_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v_fst_1773_; 
v___x_1771_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1);
v___x_1772_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1770_, v___x_1771_);
v_fst_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_fst_1773_);
lean_dec_ref(v___x_1772_);
return v_fst_1773_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(lean_object* v_00_u03c4_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_v_1777_){
_start:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(v_v_1777_);
v___x_1779_ = lean_unbox(v___x_1778_);
lean_dec(v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___boxed(lean_object* v_00_u03c4_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_v_1783_){
_start:
{
uint8_t v_res_1784_; lean_object* v_r_1785_; 
v_res_1784_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(v_00_u03c4_1780_, v_inst_1781_, v_inst_1782_, v_v_1783_);
lean_dec_ref(v_inst_1782_);
lean_dec_ref(v_inst_1781_);
v_r_1785_ = lean_box(v_res_1784_);
return v_r_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(uint8_t v_x_1786_){
_start:
{
switch(v_x_1786_)
{
case 0:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_unsigned_to_nat(0u);
return v___x_1787_;
}
case 1:
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_unsigned_to_nat(1u);
return v___x_1788_;
}
default: 
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_unsigned_to_nat(2u);
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1790_){
_start:
{
uint8_t v_x_boxed_1791_; lean_object* v_res_1792_; 
v_x_boxed_1791_ = lean_unbox(v_x_1790_);
v_res_1792_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(v_x_boxed_1791_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object* v_k_1793_){
_start:
{
lean_inc(v_k_1793_);
return v_k_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(v_k_1794_);
lean_dec(v_k_1794_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object* v_motive_1796_, lean_object* v_ctorIdx_1797_, uint8_t v_t_1798_, lean_object* v_h_1799_, lean_object* v_k_1800_){
_start:
{
lean_inc(v_k_1800_);
return v_k_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1801_, lean_object* v_ctorIdx_1802_, lean_object* v_t_1803_, lean_object* v_h_1804_, lean_object* v_k_1805_){
_start:
{
uint8_t v_t_boxed_1806_; lean_object* v_res_1807_; 
v_t_boxed_1806_ = lean_unbox(v_t_1803_);
v_res_1807_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(v_motive_1801_, v_ctorIdx_1802_, v_t_boxed_1806_, v_h_1804_, v_k_1805_);
lean_dec(v_k_1805_);
lean_dec(v_ctorIdx_1802_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1808_){
_start:
{
lean_inc(v_withoutSpacing_1808_);
return v_withoutSpacing_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1809_);
lean_dec(v_withoutSpacing_1809_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1811_, uint8_t v_t_1812_, lean_object* v_h_1813_, lean_object* v_withoutSpacing_1814_){
_start:
{
lean_inc(v_withoutSpacing_1814_);
return v_withoutSpacing_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1815_, lean_object* v_t_1816_, lean_object* v_h_1817_, lean_object* v_withoutSpacing_1818_){
_start:
{
uint8_t v_t_boxed_1819_; lean_object* v_res_1820_; 
v_t_boxed_1819_ = lean_unbox(v_t_1816_);
v_res_1820_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(v_motive_1815_, v_t_boxed_1819_, v_h_1817_, v_withoutSpacing_1818_);
lean_dec(v_withoutSpacing_1818_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object* v_withoutSpacingIfAtomic_1821_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1821_);
return v_withoutSpacingIfAtomic_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object* v_withoutSpacingIfAtomic_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(v_withoutSpacingIfAtomic_1822_);
lean_dec(v_withoutSpacingIfAtomic_1822_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object* v_motive_1824_, uint8_t v_t_1825_, lean_object* v_h_1826_, lean_object* v_withoutSpacingIfAtomic_1827_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1827_);
return v_withoutSpacingIfAtomic_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object* v_motive_1828_, lean_object* v_t_1829_, lean_object* v_h_1830_, lean_object* v_withoutSpacingIfAtomic_1831_){
_start:
{
uint8_t v_t_boxed_1832_; lean_object* v_res_1833_; 
v_t_boxed_1832_ = lean_unbox(v_t_1829_);
v_res_1833_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(v_motive_1828_, v_t_boxed_1832_, v_h_1830_, v_withoutSpacingIfAtomic_1831_);
lean_dec(v_withoutSpacingIfAtomic_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1834_){
_start:
{
lean_inc(v_withSpacing_1834_);
return v_withSpacing_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1835_);
lean_dec(v_withSpacing_1835_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object* v_motive_1837_, uint8_t v_t_1838_, lean_object* v_h_1839_, lean_object* v_withSpacing_1840_){
_start:
{
lean_inc(v_withSpacing_1840_);
return v_withSpacing_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1841_, lean_object* v_t_1842_, lean_object* v_h_1843_, lean_object* v_withSpacing_1844_){
_start:
{
uint8_t v_t_boxed_1845_; lean_object* v_res_1846_; 
v_t_boxed_1845_ = lean_unbox(v_t_1842_);
v_res_1846_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(v_motive_1841_, v_t_boxed_1845_, v_h_1843_, v_withSpacing_1844_);
lean_dec(v_withSpacing_1844_);
return v_res_1846_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_unsigned_to_nat(16u);
v___x_1849_ = lean_mk_array(v___x_1848_, v___x_1847_);
return v___x_1849_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object* v_v_1853_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v_fst_1856_; uint8_t v___x_1857_; 
v___x_1854_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1);
v___x_1855_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1853_, v___x_1854_);
v_fst_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_fst_1856_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = lean_unbox(v_fst_1856_);
lean_dec(v_fst_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object* v_v_1858_){
_start:
{
uint8_t v_res_1859_; lean_object* v_r_1860_; 
v_res_1859_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_v_1858_);
v_r_1860_ = lean_box(v_res_1859_);
return v_r_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object* v_prefixOperatorTk_1861_, lean_object* v_operand_1862_, uint8_t v_format_1863_){
_start:
{
lean_object* v___y_1865_; uint8_t v___y_1877_; uint8_t v___x_1884_; uint8_t v___y_1886_; uint8_t v___y_1889_; 
v___x_1884_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_prefixOperatorTk_1861_);
if (v___x_1884_ == 0)
{
if (v_format_1863_ == 0)
{
goto v___jp_1869_;
}
else
{
if (v___x_1884_ == 0)
{
uint8_t v___x_1890_; 
v___x_1890_ = 1;
if (v_format_1863_ == 1)
{
goto v___jp_1891_;
}
else
{
if (v___x_1884_ == 0)
{
v___y_1889_ = v___x_1884_;
goto v___jp_1888_;
}
else
{
goto v___jp_1891_;
}
}
v___jp_1891_:
{
uint8_t v___x_1892_; 
v___x_1892_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_operand_1862_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; 
lean_inc_ref(v_operand_1862_);
v___x_1893_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_operand_1862_);
v___y_1889_ = v___x_1893_;
goto v___jp_1888_;
}
else
{
v___y_1886_ = v___x_1890_;
goto v___jp_1885_;
}
}
}
else
{
goto v___jp_1869_;
}
}
}
else
{
lean_dec_ref(v_prefixOperatorTk_1861_);
return v_operand_1862_;
}
v___jp_1864_:
{
lean_object* v_doc_1866_; uint8_t v___x_1867_; 
v_doc_1866_ = lean_ctor_get(v_operand_1862_, 0);
lean_inc(v_doc_1866_);
lean_dec_ref(v_operand_1862_);
v___x_1867_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1866_);
if (v___x_1867_ == 0)
{
return v___y_1865_;
}
else
{
lean_object* v_doc_1868_; 
v_doc_1868_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___y_1865_);
return v_doc_1868_;
}
}
v___jp_1869_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1870_ = lean_unsigned_to_nat(2u);
v___x_1871_ = lean_mk_empty_array_with_capacity(v___x_1870_);
v___x_1872_ = lean_array_push(v___x_1871_, v_prefixOperatorTk_1861_);
lean_inc_ref(v_operand_1862_);
v___x_1873_ = lean_array_push(v___x_1872_, v_operand_1862_);
v___x_1874_ = l_Lean_Fmt_Layouts_atomic(v___x_1873_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1874_);
v___y_1865_ = v___x_1875_;
goto v___jp_1864_;
}
v___jp_1876_:
{
if (v___y_1877_ == 0)
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1878_ = lean_unsigned_to_nat(2u);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
v___x_1880_ = lean_array_push(v___x_1879_, v_prefixOperatorTk_1861_);
lean_inc_ref(v_operand_1862_);
v___x_1881_ = lean_array_push(v___x_1880_, v_operand_1862_);
v___x_1882_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1881_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1882_);
v___y_1865_ = v___x_1883_;
goto v___jp_1864_;
}
else
{
goto v___jp_1869_;
}
}
v___jp_1885_:
{
uint8_t v___x_1887_; 
lean_inc_ref(v_operand_1862_);
v___x_1887_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_operand_1862_);
if (v___x_1887_ == 0)
{
v___y_1877_ = v___y_1886_;
goto v___jp_1876_;
}
else
{
v___y_1877_ = v___x_1884_;
goto v___jp_1876_;
}
}
v___jp_1888_:
{
if (v___y_1889_ == 0)
{
v___y_1877_ = v___x_1884_;
goto v___jp_1876_;
}
else
{
v___y_1886_ = v___y_1889_;
goto v___jp_1885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object* v_prefixOperatorTk_1894_, lean_object* v_operand_1895_, lean_object* v_format_1896_){
_start:
{
uint8_t v_format_boxed_1897_; lean_object* v_res_1898_; 
v_format_boxed_1897_ = lean_unbox(v_format_1896_);
v_res_1898_ = l_Lean_Fmt_Layouts_prefixOperator(v_prefixOperatorTk_1894_, v_operand_1895_, v_format_boxed_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(uint8_t v_x_1899_){
_start:
{
if (v_x_1899_ == 0)
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
return v___x_1900_;
}
else
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_unsigned_to_nat(1u);
return v___x_1901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1902_){
_start:
{
uint8_t v_x_boxed_1903_; lean_object* v_res_1904_; 
v_x_boxed_1903_ = lean_unbox(v_x_1902_);
v_res_1904_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(v_x_boxed_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object* v_k_1905_){
_start:
{
lean_inc(v_k_1905_);
return v_k_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(v_k_1906_);
lean_dec(v_k_1906_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object* v_motive_1908_, lean_object* v_ctorIdx_1909_, uint8_t v_t_1910_, lean_object* v_h_1911_, lean_object* v_k_1912_){
_start:
{
lean_inc(v_k_1912_);
return v_k_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1913_, lean_object* v_ctorIdx_1914_, lean_object* v_t_1915_, lean_object* v_h_1916_, lean_object* v_k_1917_){
_start:
{
uint8_t v_t_boxed_1918_; lean_object* v_res_1919_; 
v_t_boxed_1918_ = lean_unbox(v_t_1915_);
v_res_1919_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(v_motive_1913_, v_ctorIdx_1914_, v_t_boxed_1918_, v_h_1916_, v_k_1917_);
lean_dec(v_k_1917_);
lean_dec(v_ctorIdx_1914_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1920_){
_start:
{
lean_inc(v_withoutSpacing_1920_);
return v_withoutSpacing_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1921_);
lean_dec(v_withoutSpacing_1921_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1923_, uint8_t v_t_1924_, lean_object* v_h_1925_, lean_object* v_withoutSpacing_1926_){
_start:
{
lean_inc(v_withoutSpacing_1926_);
return v_withoutSpacing_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1927_, lean_object* v_t_1928_, lean_object* v_h_1929_, lean_object* v_withoutSpacing_1930_){
_start:
{
uint8_t v_t_boxed_1931_; lean_object* v_res_1932_; 
v_t_boxed_1931_ = lean_unbox(v_t_1928_);
v_res_1932_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(v_motive_1927_, v_t_boxed_1931_, v_h_1929_, v_withoutSpacing_1930_);
lean_dec(v_withoutSpacing_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1933_){
_start:
{
lean_inc(v_withSpacing_1933_);
return v_withSpacing_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1934_);
lean_dec(v_withSpacing_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object* v_motive_1936_, uint8_t v_t_1937_, lean_object* v_h_1938_, lean_object* v_withSpacing_1939_){
_start:
{
lean_inc(v_withSpacing_1939_);
return v_withSpacing_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1940_, lean_object* v_t_1941_, lean_object* v_h_1942_, lean_object* v_withSpacing_1943_){
_start:
{
uint8_t v_t_boxed_1944_; lean_object* v_res_1945_; 
v_t_boxed_1944_ = lean_unbox(v_t_1941_);
v_res_1945_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(v_motive_1940_, v_t_boxed_1944_, v_h_1942_, v_withSpacing_1943_);
lean_dec(v_withSpacing_1943_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object* v_operand_1946_, lean_object* v_postfixOperatorTk_1947_, uint8_t v_format_1948_){
_start:
{
uint8_t v___x_1956_; 
v___x_1956_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_postfixOperatorTk_1947_);
if (v___x_1956_ == 0)
{
if (v_format_1948_ == 1)
{
goto v___jp_1949_;
}
else
{
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1957_ = lean_unsigned_to_nat(2u);
v___x_1958_ = lean_mk_empty_array_with_capacity(v___x_1957_);
v___x_1959_ = lean_array_push(v___x_1958_, v_operand_1946_);
v___x_1960_ = lean_array_push(v___x_1959_, v_postfixOperatorTk_1947_);
v___x_1961_ = l_Lean_Fmt_Layouts_atomic(v___x_1960_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1961_);
return v___x_1962_;
}
else
{
goto v___jp_1949_;
}
}
}
else
{
lean_dec_ref(v_postfixOperatorTk_1947_);
return v_operand_1946_;
}
v___jp_1949_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1950_ = lean_unsigned_to_nat(2u);
v___x_1951_ = lean_mk_empty_array_with_capacity(v___x_1950_);
v___x_1952_ = lean_array_push(v___x_1951_, v_operand_1946_);
v___x_1953_ = lean_array_push(v___x_1952_, v_postfixOperatorTk_1947_);
v___x_1954_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1953_);
lean_dec_ref(v___x_1953_);
v___x_1955_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1954_);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object* v_operand_1963_, lean_object* v_postfixOperatorTk_1964_, lean_object* v_format_1965_){
_start:
{
uint8_t v_format_boxed_1966_; lean_object* v_res_1967_; 
v_format_boxed_1966_ = lean_unbox(v_format_1965_);
v_res_1967_ = l_Lean_Fmt_Layouts_postfixOperator(v_operand_1963_, v_postfixOperatorTk_1964_, v_format_boxed_1966_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(lean_object* v_x_1968_){
_start:
{
if (lean_obj_tag(v_x_1968_) == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_unsigned_to_nat(0u);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_unsigned_to_nat(1u);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(v_x_1971_);
lean_dec_ref(v_x_1971_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object* v_t_1973_, lean_object* v_k_1974_){
_start:
{
if (lean_obj_tag(v_t_1973_) == 0)
{
uint8_t v_hardNestedFirstOperand_1975_; uint8_t v_trailingOperator_1976_; uint8_t v_spacing_1977_; uint8_t v_respectPseudoAlignment_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_hardNestedFirstOperand_1975_ = lean_ctor_get_uint8(v_t_1973_, 0);
v_trailingOperator_1976_ = lean_ctor_get_uint8(v_t_1973_, 1);
v_spacing_1977_ = lean_ctor_get_uint8(v_t_1973_, 2);
v_respectPseudoAlignment_1978_ = lean_ctor_get_uint8(v_t_1973_, 3);
v___x_1979_ = lean_box(v_hardNestedFirstOperand_1975_);
v___x_1980_ = lean_box(v_trailingOperator_1976_);
v___x_1981_ = lean_box(v_spacing_1977_);
v___x_1982_ = lean_box(v_respectPseudoAlignment_1978_);
v___x_1983_ = lean_apply_4(v_k_1974_, v___x_1979_, v___x_1980_, v___x_1981_, v___x_1982_);
return v___x_1983_;
}
else
{
uint8_t v_hardNestedFirstOperand_1984_; uint8_t v_trailingOperator_1985_; uint8_t v_spacing_1986_; uint8_t v_alignedOperators_1987_; uint8_t v_separateFinalOperand_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_hardNestedFirstOperand_1984_ = lean_ctor_get_uint8(v_t_1973_, 0);
v_trailingOperator_1985_ = lean_ctor_get_uint8(v_t_1973_, 1);
v_spacing_1986_ = lean_ctor_get_uint8(v_t_1973_, 2);
v_alignedOperators_1987_ = lean_ctor_get_uint8(v_t_1973_, 3);
v_separateFinalOperand_1988_ = lean_ctor_get_uint8(v_t_1973_, 4);
v___x_1989_ = lean_box(v_hardNestedFirstOperand_1984_);
v___x_1990_ = lean_box(v_trailingOperator_1985_);
v___x_1991_ = lean_box(v_spacing_1986_);
v___x_1992_ = lean_box(v_alignedOperators_1987_);
v___x_1993_ = lean_box(v_separateFinalOperand_1988_);
v___x_1994_ = lean_apply_5(v_k_1974_, v___x_1989_, v___x_1990_, v___x_1991_, v___x_1992_, v___x_1993_);
return v___x_1994_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_t_1995_, lean_object* v_k_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1995_, v_k_1996_);
lean_dec_ref(v_t_1995_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object* v_motive_1998_, lean_object* v_ctorIdx_1999_, lean_object* v_t_2000_, lean_object* v_h_2001_, lean_object* v_k_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2000_, v_k_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_2004_, lean_object* v_ctorIdx_2005_, lean_object* v_t_2006_, lean_object* v_h_2007_, lean_object* v_k_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(v_motive_2004_, v_ctorIdx_2005_, v_t_2006_, v_h_2007_, v_k_2008_);
lean_dec_ref(v_t_2006_);
lean_dec(v_ctorIdx_2005_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object* v_t_2010_, lean_object* v_dense_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2010_, v_dense_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object* v_t_2013_, lean_object* v_dense_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(v_t_2013_, v_dense_2014_);
lean_dec_ref(v_t_2013_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object* v_motive_2016_, lean_object* v_t_2017_, lean_object* v_h_2018_, lean_object* v_dense_2019_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2017_, v_dense_2019_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object* v_motive_2021_, lean_object* v_t_2022_, lean_object* v_h_2023_, lean_object* v_dense_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(v_motive_2021_, v_t_2022_, v_h_2023_, v_dense_2024_);
lean_dec_ref(v_t_2022_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object* v_t_2026_, lean_object* v_sparse_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2026_, v_sparse_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object* v_t_2029_, lean_object* v_sparse_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(v_t_2029_, v_sparse_2030_);
lean_dec_ref(v_t_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object* v_motive_2032_, lean_object* v_t_2033_, lean_object* v_h_2034_, lean_object* v_sparse_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2033_, v_sparse_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object* v_motive_2037_, lean_object* v_t_2038_, lean_object* v_h_2039_, lean_object* v_sparse_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(v_motive_2037_, v_t_2038_, v_h_2039_, v_sparse_2040_);
lean_dec_ref(v_t_2038_);
return v_res_2041_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object* v_x_2042_){
_start:
{
uint8_t v_hardNestedFirstOperand_2043_; 
v_hardNestedFirstOperand_2043_ = lean_ctor_get_uint8(v_x_2042_, 0);
return v_hardNestedFirstOperand_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object* v_x_2044_){
_start:
{
uint8_t v_res_2045_; lean_object* v_r_2046_; 
v_res_2045_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(v_x_2044_);
lean_dec_ref(v_x_2044_);
v_r_2046_ = lean_box(v_res_2045_);
return v_r_2046_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object* v_x_2047_){
_start:
{
uint8_t v_trailingOperator_2048_; 
v_trailingOperator_2048_ = lean_ctor_get_uint8(v_x_2047_, 1);
return v_trailingOperator_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object* v_x_2049_){
_start:
{
uint8_t v_res_2050_; lean_object* v_r_2051_; 
v_res_2050_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(v_x_2049_);
lean_dec_ref(v_x_2049_);
v_r_2051_ = lean_box(v_res_2050_);
return v_r_2051_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object* v_x_2052_){
_start:
{
uint8_t v_spacing_2053_; 
v_spacing_2053_ = lean_ctor_get_uint8(v_x_2052_, 2);
return v_spacing_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object* v_x_2054_){
_start:
{
uint8_t v_res_2055_; lean_object* v_r_2056_; 
v_res_2055_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(v_x_2054_);
lean_dec_ref(v_x_2054_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(lean_object* v_x_2057_){
_start:
{
if (lean_obj_tag(v_x_2057_) == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = 0;
return v___x_2058_;
}
else
{
uint8_t v_trailingOperator_2059_; 
v_trailingOperator_2059_ = lean_ctor_get_uint8(v_x_2057_, 1);
if (v_trailingOperator_2059_ == 0)
{
uint8_t v_alignedOperators_2060_; 
v_alignedOperators_2060_ = lean_ctor_get_uint8(v_x_2057_, 3);
return v_alignedOperators_2060_;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = 0;
return v___x_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators___boxed(lean_object* v_x_2062_){
_start:
{
uint8_t v_res_2063_; lean_object* v_r_2064_; 
v_res_2063_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_x_2062_);
lean_dec_ref(v_x_2062_);
v_r_2064_ = lean_box(v_res_2063_);
return v_r_2064_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(lean_object* v_x_2065_){
_start:
{
if (lean_obj_tag(v_x_2065_) == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = 0;
return v___x_2066_;
}
else
{
uint8_t v_trailingOperator_2067_; 
v_trailingOperator_2067_ = lean_ctor_get_uint8(v_x_2065_, 1);
if (v_trailingOperator_2067_ == 0)
{
uint8_t v_separateFinalOperand_2068_; 
v_separateFinalOperand_2068_ = lean_ctor_get_uint8(v_x_2065_, 4);
return v_separateFinalOperand_2068_;
}
else
{
uint8_t v___x_2069_; 
v___x_2069_ = 0;
return v___x_2069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand___boxed(lean_object* v_x_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_x_2070_);
lean_dec_ref(v_x_2070_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(lean_object* v_x_2073_){
_start:
{
if (lean_obj_tag(v_x_2073_) == 0)
{
uint8_t v_respectPseudoAlignment_2074_; 
v_respectPseudoAlignment_2074_ = lean_ctor_get_uint8(v_x_2073_, 3);
return v_respectPseudoAlignment_2074_;
}
else
{
uint8_t v___x_2075_; 
v___x_2075_ = 1;
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment___boxed(lean_object* v_x_2076_){
_start:
{
uint8_t v_res_2077_; lean_object* v_r_2078_; 
v_res_2077_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_x_2076_);
lean_dec_ref(v_x_2076_);
v_r_2078_ = lean_box(v_res_2077_);
return v_r_2078_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object* v_doc_2079_, uint8_t v_respectPseudoAlignment_2080_){
_start:
{
if (v_respectPseudoAlignment_2080_ == 0)
{
lean_object* v_doc_2081_; uint8_t v___x_2082_; 
v_doc_2081_ = lean_ctor_get(v_doc_2079_, 0);
lean_inc(v_doc_2081_);
lean_dec_ref(v_doc_2079_);
v___x_2082_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
v___x_2083_ = 1;
return v___x_2083_;
}
else
{
return v_respectPseudoAlignment_2080_;
}
}
else
{
uint8_t v___x_2084_; 
lean_inc_ref(v_doc_2079_);
v___x_2084_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_2079_);
if (v___x_2084_ == 0)
{
lean_object* v_doc_2085_; uint8_t v___x_2086_; 
v_doc_2085_ = lean_ctor_get(v_doc_2079_, 0);
lean_inc(v_doc_2085_);
lean_dec_ref(v_doc_2079_);
v___x_2086_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2085_);
if (v___x_2086_ == 0)
{
return v_respectPseudoAlignment_2080_;
}
else
{
return v___x_2084_;
}
}
else
{
uint8_t v___x_2087_; 
lean_dec_ref(v_doc_2079_);
v___x_2087_ = 0;
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object* v_doc_2088_, lean_object* v_respectPseudoAlignment_2089_){
_start:
{
uint8_t v_respectPseudoAlignment_boxed_2090_; uint8_t v_res_2091_; lean_object* v_r_2092_; 
v_respectPseudoAlignment_boxed_2090_ = lean_unbox(v_respectPseudoAlignment_2089_);
v_res_2091_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_doc_2088_, v_respectPseudoAlignment_boxed_2090_);
v_r_2092_ = lean_box(v_res_2091_);
return v_r_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object* v_format_2093_, lean_object* v_docs_2094_){
_start:
{
uint8_t v___y_2096_; uint8_t v_spacing_2099_; 
v_spacing_2099_ = lean_ctor_get_uint8(v_format_2093_, 2);
v___y_2096_ = v_spacing_2099_;
goto v___jp_2095_;
v___jp_2095_:
{
if (v___y_2096_ == 0)
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_Fmt_Layouts_atomic(v_docs_2094_);
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_Fmt_Layouts_spacedAtomic(v_docs_2094_);
return v___x_2098_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object* v_format_2100_, lean_object* v_docs_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2100_, v_docs_2101_);
lean_dec_ref(v_docs_2101_);
lean_dec_ref(v_format_2100_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object* v_msg_2103_){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_2105_ = lean_panic_fn_borrowed(v___x_2104_, v_msg_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t v_a_2106_, lean_object* v_as_2107_, size_t v_i_2108_, size_t v_stop_2109_){
_start:
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_usize_dec_eq(v_i_2108_, v_stop_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = lean_array_uget_borrowed(v_as_2107_, v_i_2108_);
v___x_2112_ = lean_unbox(v___x_2111_);
v___x_2113_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_a_2106_, v___x_2112_);
if (v___x_2113_ == 0)
{
size_t v___x_2114_; size_t v___x_2115_; 
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2108_, v___x_2114_);
v_i_2108_ = v___x_2115_;
goto _start;
}
else
{
return v___x_2113_;
}
}
else
{
uint8_t v___x_2117_; 
v___x_2117_ = 0;
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object* v_a_2118_, lean_object* v_as_2119_, lean_object* v_i_2120_, lean_object* v_stop_2121_){
_start:
{
uint8_t v_a_boxed_2122_; size_t v_i_boxed_2123_; size_t v_stop_boxed_2124_; uint8_t v_res_2125_; lean_object* v_r_2126_; 
v_a_boxed_2122_ = lean_unbox(v_a_2118_);
v_i_boxed_2123_ = lean_unbox_usize(v_i_2120_);
lean_dec(v_i_2120_);
v_stop_boxed_2124_ = lean_unbox_usize(v_stop_2121_);
lean_dec(v_stop_2121_);
v_res_2125_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_boxed_2122_, v_as_2119_, v_i_boxed_2123_, v_stop_boxed_2124_);
lean_dec_ref(v_as_2119_);
v_r_2126_ = lean_box(v_res_2125_);
return v_r_2126_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object* v_as_2127_, uint8_t v_a_2128_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = lean_array_get_size(v_as_2127_);
v___x_2131_ = lean_nat_dec_lt(v___x_2129_, v___x_2130_);
if (v___x_2131_ == 0)
{
return v___x_2131_;
}
else
{
if (v___x_2131_ == 0)
{
return v___x_2131_;
}
else
{
size_t v___x_2132_; size_t v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = lean_usize_of_nat(v___x_2130_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_2128_, v_as_2127_, v___x_2132_, v___x_2133_);
return v___x_2134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object* v_as_2135_, lean_object* v_a_2136_){
_start:
{
uint8_t v_a_boxed_2137_; uint8_t v_res_2138_; lean_object* v_r_2139_; 
v_a_boxed_2137_ = lean_unbox(v_a_2136_);
v_res_2138_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_as_2135_, v_a_boxed_2137_);
lean_dec_ref(v_as_2135_);
v_r_2139_ = lean_box(v_res_2138_);
return v_r_2139_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2));
v___x_2144_ = lean_unsigned_to_nat(14u);
v___x_2145_ = lean_unsigned_to_nat(22u);
v___x_2146_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1));
v___x_2147_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_2148_ = l_mkPanicMessageWithDecl(v___x_2147_, v___x_2146_, v___x_2145_, v___x_2144_, v___x_2143_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object* v_format_2149_, lean_object* v_doc_2150_, lean_object* v_lastOperand_2151_, uint8_t v_isTailless_2152_, lean_object* v_combinedChain_2153_, lean_object* v_eligibleKinds_2154_){
_start:
{
lean_object* v___x_2155_; uint8_t v___y_2157_; lean_object* v___y_2158_; uint8_t v___y_2179_; uint8_t v_trailingOperator_2192_; 
v___x_2155_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2192_ = lean_ctor_get_uint8(v_format_2149_, 1);
v___y_2179_ = v_trailingOperator_2192_;
goto v___jp_2178_;
v___jp_2156_:
{
lean_object* v_stickyVariant_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_stickyVariant_2159_ = lean_ctor_get(v___y_2158_, 0);
v___x_2160_ = lean_array_get_size(v_combinedChain_2153_);
v___x_2161_ = lean_unsigned_to_nat(1u);
v___x_2162_ = lean_nat_sub(v___x_2160_, v___x_2161_);
lean_inc_ref(v_stickyVariant_2159_);
v___x_2163_ = lean_array_set(v_combinedChain_2153_, v___x_2162_, v_stickyVariant_2159_);
lean_dec(v___x_2162_);
lean_inc_ref(v___x_2163_);
v___x_2164_ = lean_array_pop(v___x_2163_);
v___x_2165_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2149_, v___x_2164_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_2165_);
v___x_2167_ = lean_array_get_size(v___x_2163_);
v___x_2168_ = lean_nat_sub(v___x_2167_, v___x_2161_);
v___x_2169_ = lean_array_get(v___x_2155_, v___x_2163_, v___x_2168_);
lean_dec(v___x_2168_);
lean_dec_ref(v___x_2163_);
v___x_2170_ = lean_unsigned_to_nat(2u);
v___x_2171_ = lean_mk_empty_array_with_capacity(v___x_2170_);
v___x_2172_ = lean_array_push(v___x_2171_, v___x_2166_);
v___x_2173_ = lean_array_push(v___x_2172_, v___x_2169_);
v___x_2174_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2149_, v___x_2173_);
lean_dec_ref(v___x_2173_);
v___x_2175_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_2158_, v___y_2157_);
lean_dec_ref(v___y_2158_);
v___x_2176_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_2150_, v___x_2174_, v___x_2175_);
lean_dec(v___x_2175_);
v___x_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
v___jp_2178_:
{
if (v___y_2179_ == 0)
{
lean_object* v___x_2180_; 
lean_dec_ref(v_combinedChain_2153_);
lean_dec_ref(v_lastOperand_2151_);
lean_dec_ref(v_doc_2150_);
v___x_2180_ = lean_box(0);
return v___x_2180_;
}
else
{
if (v_isTailless_2152_ == 0)
{
lean_object* v___x_2181_; 
lean_inc_ref(v_lastOperand_2151_);
v___x_2181_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v_lastOperand_2151_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v___x_2182_; 
lean_dec_ref(v_combinedChain_2153_);
lean_dec_ref(v_lastOperand_2151_);
lean_dec_ref(v_doc_2150_);
v___x_2182_ = lean_box(0);
return v___x_2182_;
}
else
{
lean_object* v_val_2183_; uint8_t v___x_2184_; uint8_t v___x_2185_; 
v_val_2183_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2184_ = lean_unbox(v_val_2183_);
lean_dec(v_val_2183_);
v___x_2185_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_2154_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_dec_ref(v_combinedChain_2153_);
lean_dec_ref(v_lastOperand_2151_);
lean_dec_ref(v_doc_2150_);
v___x_2186_ = lean_box(0);
return v___x_2186_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_lastOperand_2151_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_2189_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_2188_);
v___y_2157_ = v___x_2185_;
v___y_2158_ = v___x_2189_;
goto v___jp_2156_;
}
else
{
lean_object* v_val_2190_; 
v_val_2190_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_val_2190_);
lean_dec_ref_known(v___x_2187_, 1);
v___y_2157_ = v___x_2185_;
v___y_2158_ = v_val_2190_;
goto v___jp_2156_;
}
}
}
}
else
{
lean_object* v___x_2191_; 
lean_dec_ref(v_combinedChain_2153_);
lean_dec_ref(v_lastOperand_2151_);
lean_dec_ref(v_doc_2150_);
v___x_2191_ = lean_box(0);
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object* v_format_2193_, lean_object* v_doc_2194_, lean_object* v_lastOperand_2195_, lean_object* v_isTailless_2196_, lean_object* v_combinedChain_2197_, lean_object* v_eligibleKinds_2198_){
_start:
{
uint8_t v_isTailless_boxed_2199_; lean_object* v_res_2200_; 
v_isTailless_boxed_2199_ = lean_unbox(v_isTailless_2196_);
v_res_2200_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2193_, v_doc_2194_, v_lastOperand_2195_, v_isTailless_boxed_2199_, v_combinedChain_2197_, v_eligibleKinds_2198_);
lean_dec_ref(v_eligibleKinds_2198_);
lean_dec_ref(v_format_2193_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object* v_format_2201_, lean_object* v_doc_2202_, lean_object* v_lastOperand_2203_, uint8_t v_isTailless_2204_, lean_object* v_combinedChain_2205_){
_start:
{
if (lean_obj_tag(v_format_2201_) == 0)
{
if (v_isTailless_2204_ == 0)
{
uint8_t v_trailingOperator_2206_; lean_object* v___x_2207_; 
v_trailingOperator_2206_ = lean_ctor_get_uint8(v_format_2201_, 1);
v___x_2207_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
if (v_trailingOperator_2206_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2226_ = lean_array_get_size(v_combinedChain_2205_);
v___x_2227_ = lean_unsigned_to_nat(2u);
v___x_2228_ = lean_nat_dec_eq(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2229_; 
lean_dec_ref(v_combinedChain_2205_);
lean_dec_ref(v_lastOperand_2203_);
lean_dec_ref(v_doc_2202_);
v___x_2229_ = lean_box(0);
return v___x_2229_;
}
else
{
goto v___jp_2208_;
}
}
else
{
goto v___jp_2208_;
}
v___jp_2208_:
{
uint8_t v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_respectPseudoAlignment(v_format_2201_);
v___x_2210_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_lastOperand_2203_, v___x_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
lean_dec_ref(v_combinedChain_2205_);
lean_dec_ref(v_doc_2202_);
v___x_2211_ = lean_box(0);
return v___x_2211_;
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_inc_ref(v_combinedChain_2205_);
v___x_2212_ = lean_array_pop(v_combinedChain_2205_);
v___x_2213_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2201_, v___x_2212_);
lean_dec_ref(v___x_2212_);
v___x_2214_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_2213_);
v___x_2215_ = lean_array_get_size(v_combinedChain_2205_);
v___x_2216_ = lean_unsigned_to_nat(1u);
v___x_2217_ = lean_nat_sub(v___x_2215_, v___x_2216_);
v___x_2218_ = lean_array_get(v___x_2207_, v_combinedChain_2205_, v___x_2217_);
lean_dec(v___x_2217_);
lean_dec_ref(v_combinedChain_2205_);
v___x_2219_ = lean_unsigned_to_nat(2u);
v___x_2220_ = lean_mk_empty_array_with_capacity(v___x_2219_);
v___x_2221_ = lean_array_push(v___x_2220_, v___x_2214_);
v___x_2222_ = lean_array_push(v___x_2221_, v___x_2218_);
v___x_2223_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2201_, v___x_2222_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = l_Lean_Fmt_TaggedDoc_fallbackOnHeight(v_doc_2202_, v___x_2223_);
v___x_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
return v___x_2225_;
}
}
}
else
{
lean_object* v___x_2230_; 
lean_dec_ref(v_combinedChain_2205_);
lean_dec_ref(v_lastOperand_2203_);
lean_dec_ref(v_doc_2202_);
v___x_2230_ = lean_box(0);
return v___x_2230_;
}
}
else
{
lean_object* v___x_2231_; 
lean_dec_ref(v_combinedChain_2205_);
lean_dec_ref(v_lastOperand_2203_);
lean_dec_ref(v_doc_2202_);
v___x_2231_ = lean_box(0);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object* v_format_2232_, lean_object* v_doc_2233_, lean_object* v_lastOperand_2234_, lean_object* v_isTailless_2235_, lean_object* v_combinedChain_2236_){
_start:
{
uint8_t v_isTailless_boxed_2237_; lean_object* v_res_2238_; 
v_isTailless_boxed_2237_ = lean_unbox(v_isTailless_2235_);
v_res_2238_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2232_, v_doc_2233_, v_lastOperand_2234_, v_isTailless_boxed_2237_, v_combinedChain_2236_);
lean_dec_ref(v_format_2232_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object* v_snd_2239_, lean_object* v___x_2240_, lean_object* v_____r_2241_, lean_object* v_normalized_2242_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_nat_add(v_snd_2239_, v___x_2240_);
v___x_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2244_, 0, v_normalized_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object* v_snd_2246_, lean_object* v___x_2247_, lean_object* v_____r_2248_, lean_object* v_normalized_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2246_, v___x_2247_, v_____r_2248_, v_normalized_2249_);
lean_dec(v___x_2247_);
lean_dec(v_snd_2246_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object* v___x_2251_, lean_object* v_chain_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v___y_2255_; lean_object* v_fst_2259_; lean_object* v_snd_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2287_; 
v_fst_2259_ = lean_ctor_get(v_a_2253_, 0);
v_snd_2260_ = lean_ctor_get(v_a_2253_, 1);
v_isSharedCheck_2287_ = !lean_is_exclusive(v_a_2253_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2262_ = v_a_2253_;
v_isShared_2263_ = v_isSharedCheck_2287_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_snd_2260_);
lean_inc(v_fst_2259_);
lean_dec(v_a_2253_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2287_;
goto v_resetjp_2261_;
}
v___jp_2254_:
{
if (lean_obj_tag(v___y_2255_) == 0)
{
lean_object* v_a_2256_; 
v_a_2256_ = lean_ctor_get(v___y_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___y_2255_, 1);
return v_a_2256_;
}
else
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___y_2255_, 0);
lean_inc(v_a_2257_);
lean_dec_ref_known(v___y_2255_, 1);
v_a_2253_ = v_a_2257_;
goto _start;
}
}
v_resetjp_2261_:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_nat_dec_lt(v_snd_2260_, v___x_2251_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2266_; 
if (v_isShared_2263_ == 0)
{
v___x_2266_ = v___x_2262_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_fst_2259_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v_snd_2260_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2268_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2269_ = lean_array_get_borrowed(v___x_2268_, v_chain_2252_, v_snd_2260_);
v___x_2270_ = lean_unsigned_to_nat(1u);
v___x_2271_ = lean_nat_add(v_snd_2260_, v___x_2270_);
v___x_2272_ = lean_array_get_size(v_chain_2252_);
v___x_2273_ = lean_nat_dec_lt(v___x_2271_, v___x_2272_);
if (v___x_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
lean_dec(v___x_2271_);
lean_inc(v___x_2269_);
v___x_2274_ = lean_array_push(v_fst_2259_, v___x_2269_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2274_);
v___x_2276_ = v___x_2262_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2277_, 1, v_snd_2260_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
lean_del_object(v___x_2262_);
v___x_2278_ = lean_unsigned_to_nat(2u);
v___x_2279_ = lean_array_fget_borrowed(v_chain_2252_, v___x_2271_);
lean_dec(v___x_2271_);
v___x_2280_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_inc(v___x_2269_);
v___x_2281_ = lean_array_push(v_fst_2259_, v___x_2269_);
lean_inc(v___x_2279_);
v___x_2282_ = lean_array_push(v___x_2281_, v___x_2279_);
v___x_2283_ = lean_box(0);
v___x_2284_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2260_, v___x_2278_, v___x_2283_, v___x_2282_);
lean_dec(v_snd_2260_);
v___y_2255_ = v___x_2284_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_box(0);
v___x_2286_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2260_, v___x_2278_, v___x_2285_, v_fst_2259_);
lean_dec(v_snd_2260_);
v___y_2255_ = v___x_2286_;
goto v___jp_2254_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object* v___x_2288_, lean_object* v_chain_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2288_, v_chain_2289_, v_a_2290_);
lean_dec_ref(v_chain_2289_);
lean_dec(v___x_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object* v___x_2292_, lean_object* v_chain_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___y_2296_; lean_object* v_fst_2300_; lean_object* v_snd_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2328_; 
v_fst_2300_ = lean_ctor_get(v_a_2294_, 0);
v_snd_2301_ = lean_ctor_get(v_a_2294_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_a_2294_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2303_ = v_a_2294_;
v_isShared_2304_ = v_isSharedCheck_2328_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_snd_2301_);
lean_inc(v_fst_2300_);
lean_dec(v_a_2294_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2328_;
goto v_resetjp_2302_;
}
v___jp_2295_:
{
if (lean_obj_tag(v___y_2296_) == 0)
{
lean_object* v_a_2297_; 
v_a_2297_ = lean_ctor_get(v___y_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___y_2296_, 1);
return v_a_2297_;
}
else
{
lean_object* v_a_2298_; 
v_a_2298_ = lean_ctor_get(v___y_2296_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___y_2296_, 1);
v_a_2294_ = v_a_2298_;
goto _start;
}
}
v_resetjp_2302_:
{
uint8_t v___x_2305_; 
v___x_2305_ = lean_nat_dec_lt(v_snd_2301_, v___x_2292_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2307_; 
if (v_isShared_2304_ == 0)
{
v___x_2307_ = v___x_2303_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_fst_2300_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_snd_2301_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2309_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2310_ = lean_array_get_borrowed(v___x_2309_, v_chain_2293_, v_snd_2301_);
v___x_2311_ = lean_unsigned_to_nat(1u);
v___x_2312_ = lean_nat_add(v_snd_2301_, v___x_2311_);
v___x_2313_ = lean_array_get_size(v_chain_2293_);
v___x_2314_ = lean_nat_dec_lt(v___x_2312_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2317_; 
lean_dec(v___x_2312_);
lean_inc(v___x_2310_);
v___x_2315_ = lean_array_push(v_fst_2300_, v___x_2310_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2315_);
v___x_2317_ = v___x_2303_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_snd_2301_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
else
{
lean_object* v___x_2319_; uint8_t v___x_2320_; 
lean_del_object(v___x_2303_);
v___x_2319_ = lean_unsigned_to_nat(2u);
v___x_2320_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2310_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2321_ = lean_array_fget_borrowed(v_chain_2293_, v___x_2312_);
lean_dec(v___x_2312_);
lean_inc(v___x_2310_);
v___x_2322_ = lean_array_push(v_fst_2300_, v___x_2310_);
lean_inc(v___x_2321_);
v___x_2323_ = lean_array_push(v___x_2322_, v___x_2321_);
v___x_2324_ = lean_box(0);
v___x_2325_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2301_, v___x_2319_, v___x_2324_, v___x_2323_);
lean_dec(v_snd_2301_);
v___y_2296_ = v___x_2325_;
goto v___jp_2295_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v___x_2312_);
v___x_2326_ = lean_box(0);
v___x_2327_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2301_, v___x_2319_, v___x_2326_, v_fst_2300_);
lean_dec(v_snd_2301_);
v___y_2296_ = v___x_2327_;
goto v___jp_2295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object* v___x_2329_, lean_object* v_chain_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2329_, v_chain_2330_, v_a_2331_);
lean_dec_ref(v_chain_2330_);
lean_dec(v___x_2329_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object* v_format_2341_, lean_object* v_chain_2342_){
_start:
{
uint8_t v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; uint8_t v___y_2347_; lean_object* v___y_2348_; lean_object* v___y_2349_; uint8_t v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; uint8_t v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___f_2385_; lean_object* v___x_2386_; lean_object* v_chainSizeBeforeSuffixTrim_2387_; lean_object* v_chain_2388_; lean_object* v_chainSizeBeforePrefixTrim_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; uint8_t v___y_2399_; lean_object* v___y_2411_; lean_object* v___y_2412_; uint8_t v___y_2413_; uint8_t v___y_2414_; uint8_t v___y_2419_; uint8_t v___x_2429_; 
v___f_2385_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0));
v___x_2386_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_chainSizeBeforeSuffixTrim_2387_ = lean_array_get_size(v_chain_2342_);
v_chain_2388_ = l_Array_popWhile___redArg(v___f_2385_, v_chain_2342_);
v_chainSizeBeforePrefixTrim_2389_ = lean_array_get_size(v_chain_2388_);
v___x_2390_ = lean_nat_sub(v_chainSizeBeforeSuffixTrim_2387_, v_chainSizeBeforePrefixTrim_2389_);
v___x_2391_ = lean_unsigned_to_nat(2u);
v___x_2392_ = lean_nat_mod(v___x_2390_, v___x_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_unsigned_to_nat(0u);
v___x_2429_ = lean_nat_dec_eq(v___x_2392_, v___x_2393_);
lean_dec(v___x_2392_);
if (v___x_2429_ == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = 1;
v___y_2419_ = v___x_2430_;
goto v___jp_2418_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = 0;
v___y_2419_ = v___x_2431_;
goto v___jp_2418_;
}
v___jp_2343_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v_fst_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2362_; 
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___y_2348_);
lean_ctor_set(v___x_2350_, 1, v___y_2349_);
v___x_2351_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___y_2346_, v___y_2345_, v___x_2350_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2346_);
v_fst_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v___x_2351_, 1);
lean_dec(v_unused_2363_);
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_fst_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2356_ = lean_box(v___y_2344_);
v___x_2357_ = lean_box(v___y_2347_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 1, v___x_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2356_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; 
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v_fst_2352_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
return v___x_2360_;
}
}
}
v___jp_2364_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v_fst_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2383_; 
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___y_2369_);
lean_ctor_set(v___x_2371_, 1, v___y_2370_);
v___x_2372_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___y_2367_, v___y_2366_, v___x_2371_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2367_);
v_fst_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; 
v_unused_2384_ = lean_ctor_get(v___x_2372_, 1);
lean_dec(v_unused_2384_);
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2383_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_fst_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2383_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2377_ = lean_box(v___y_2365_);
v___x_2378_ = lean_box(v___y_2368_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 1, v___x_2378_);
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2380_ = v___x_2375_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; 
v___x_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2381_, 0, v_fst_2373_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
return v___x_2381_;
}
}
}
v___jp_2394_:
{
if (v___y_2399_ == 0)
{
if (v___y_2395_ == 0)
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2400_ = lean_array_get_borrowed(v___x_2386_, v___y_2396_, v___x_2393_);
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_mk_empty_array_with_capacity(v___x_2401_);
lean_inc(v___x_2400_);
v___x_2403_ = lean_array_push(v___x_2402_, v___x_2400_);
v___y_2365_ = v___y_2395_;
v___y_2366_ = v___y_2396_;
v___y_2367_ = v___y_2397_;
v___y_2368_ = v___y_2398_;
v___y_2369_ = v___x_2403_;
v___y_2370_ = v___x_2401_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2404_; 
v___x_2404_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2365_ = v___y_2395_;
v___y_2366_ = v___y_2396_;
v___y_2367_ = v___y_2397_;
v___y_2368_ = v___y_2398_;
v___y_2369_ = v___x_2404_;
v___y_2370_ = v___x_2393_;
goto v___jp_2364_;
}
}
else
{
if (v___y_2395_ == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2344_ = v___y_2395_;
v___y_2345_ = v___y_2396_;
v___y_2346_ = v___y_2397_;
v___y_2347_ = v___y_2398_;
v___y_2348_ = v___x_2405_;
v___y_2349_ = v___x_2393_;
goto v___jp_2343_;
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2406_ = lean_array_get_borrowed(v___x_2386_, v___y_2396_, v___x_2393_);
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_mk_empty_array_with_capacity(v___x_2407_);
lean_inc(v___x_2406_);
v___x_2409_ = lean_array_push(v___x_2408_, v___x_2406_);
v___y_2344_ = v___y_2395_;
v___y_2345_ = v___y_2396_;
v___y_2346_ = v___y_2397_;
v___y_2347_ = v___y_2398_;
v___y_2348_ = v___x_2409_;
v___y_2349_ = v___x_2407_;
goto v___jp_2343_;
}
}
}
v___jp_2410_:
{
uint8_t v___x_2415_; 
v___x_2415_ = lean_nat_dec_eq(v___y_2412_, v___x_2393_);
if (v___x_2415_ == 0)
{
uint8_t v_trailingOperator_2416_; 
v_trailingOperator_2416_ = lean_ctor_get_uint8(v_format_2341_, 1);
v___y_2395_ = v___y_2414_;
v___y_2396_ = v___y_2411_;
v___y_2397_ = v___y_2412_;
v___y_2398_ = v___y_2413_;
v___y_2399_ = v_trailingOperator_2416_;
goto v___jp_2394_;
}
else
{
lean_object* v___x_2417_; 
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
v___x_2417_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2));
return v___x_2417_;
}
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v_chain_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2420_ = l_Array_reverse___redArg(v_chain_2388_);
v___x_2421_ = l_Array_popWhile___redArg(v___f_2385_, v___x_2420_);
v_chain_2422_ = l_Array_reverse___redArg(v___x_2421_);
v___x_2423_ = lean_array_get_size(v_chain_2422_);
v___x_2424_ = lean_nat_sub(v_chainSizeBeforePrefixTrim_2389_, v___x_2423_);
v___x_2425_ = lean_nat_mod(v___x_2424_, v___x_2391_);
lean_dec(v___x_2424_);
v___x_2426_ = lean_nat_dec_eq(v___x_2425_, v___x_2393_);
lean_dec(v___x_2425_);
if (v___x_2426_ == 0)
{
uint8_t v___x_2427_; 
v___x_2427_ = 1;
v___y_2411_ = v_chain_2422_;
v___y_2412_ = v___x_2423_;
v___y_2413_ = v___y_2419_;
v___y_2414_ = v___x_2427_;
goto v___jp_2410_;
}
else
{
uint8_t v___x_2428_; 
v___x_2428_ = 0;
v___y_2411_ = v_chain_2422_;
v___y_2412_ = v___x_2423_;
v___y_2413_ = v___y_2419_;
v___y_2414_ = v___x_2428_;
goto v___jp_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object* v_format_2432_, lean_object* v_chain_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2432_, v_chain_2433_);
lean_dec_ref(v_format_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object* v___x_2435_, lean_object* v_chain_2436_, lean_object* v_inst_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2435_, v_chain_2436_, v_a_2438_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object* v___x_2440_, lean_object* v_chain_2441_, lean_object* v_inst_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(v___x_2440_, v_chain_2441_, v_inst_2442_, v_a_2443_);
lean_dec_ref(v_chain_2441_);
lean_dec(v___x_2440_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object* v___x_2445_, lean_object* v_chain_2446_, lean_object* v_inst_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2445_, v_chain_2446_, v_a_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object* v___x_2450_, lean_object* v_chain_2451_, lean_object* v_inst_2452_, lean_object* v_a_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(v___x_2450_, v_chain_2451_, v_inst_2452_, v_a_2453_);
lean_dec_ref(v_chain_2451_);
lean_dec(v___x_2450_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object* v_chain_2455_, lean_object* v_format_2456_, lean_object* v_a_2457_){
_start:
{
lean_object* v_fst_2458_; lean_object* v_snd_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2489_; 
v_fst_2458_ = lean_ctor_get(v_a_2457_, 0);
v_snd_2459_ = lean_ctor_get(v_a_2457_, 1);
v_isSharedCheck_2489_ = !lean_is_exclusive(v_a_2457_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2461_ = v_a_2457_;
v_isShared_2462_ = v_isSharedCheck_2489_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_snd_2459_);
lean_inc(v_fst_2458_);
lean_dec(v_a_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2489_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; uint8_t v___x_2464_; 
v___x_2463_ = lean_array_get_size(v_chain_2455_);
v___x_2464_ = lean_nat_dec_lt(v_snd_2459_, v___x_2463_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2466_; 
if (v_isShared_2462_ == 0)
{
v___x_2466_ = v___x_2461_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_fst_2458_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_snd_2459_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___y_2471_; lean_object* v___x_2484_; lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2468_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2469_ = lean_array_get_borrowed(v___x_2468_, v_chain_2455_, v_snd_2459_);
v___x_2484_ = lean_unsigned_to_nat(1u);
v___x_2485_ = lean_nat_add(v_snd_2459_, v___x_2484_);
v___x_2486_ = lean_nat_dec_lt(v___x_2485_, v___x_2463_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec(v___x_2485_);
v___x_2487_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2471_ = v___x_2487_;
goto v___jp_2470_;
}
else
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_array_fget_borrowed(v_chain_2455_, v___x_2485_);
lean_dec(v___x_2485_);
lean_inc(v___x_2488_);
v___y_2471_ = v___x_2488_;
goto v___jp_2470_;
}
v___jp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2472_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2471_);
v___x_2473_ = lean_unsigned_to_nat(2u);
v___x_2474_ = lean_mk_empty_array_with_capacity(v___x_2473_);
lean_inc(v___x_2469_);
v___x_2475_ = lean_array_push(v___x_2474_, v___x_2469_);
v___x_2476_ = lean_array_push(v___x_2475_, v___x_2472_);
v___x_2477_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2456_, v___x_2476_);
lean_dec_ref(v___x_2476_);
v___x_2478_ = lean_array_push(v_fst_2458_, v___x_2477_);
v___x_2479_ = lean_nat_add(v_snd_2459_, v___x_2473_);
lean_dec(v_snd_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 1, v___x_2479_);
lean_ctor_set(v___x_2461_, 0, v___x_2478_);
v___x_2481_ = v___x_2461_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
v_a_2457_ = v___x_2481_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object* v_chain_2490_, lean_object* v_format_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2490_, v_format_2491_, v_a_2492_);
lean_dec_ref(v_format_2491_);
lean_dec_ref(v_chain_2490_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object* v_chain_2494_, lean_object* v_format_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_fst_2497_; lean_object* v_snd_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2528_; 
v_fst_2497_ = lean_ctor_get(v_a_2496_, 0);
v_snd_2498_ = lean_ctor_get(v_a_2496_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_a_2496_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2500_ = v_a_2496_;
v_isShared_2501_ = v_isSharedCheck_2528_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_snd_2498_);
lean_inc(v_fst_2497_);
lean_dec(v_a_2496_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2528_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; uint8_t v___x_2503_; 
v___x_2502_ = lean_array_get_size(v_chain_2494_);
v___x_2503_ = lean_nat_dec_lt(v_snd_2498_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2505_; 
if (v_isShared_2501_ == 0)
{
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_fst_2497_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_snd_2498_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___y_2510_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v___x_2507_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2508_ = lean_array_get_borrowed(v___x_2507_, v_chain_2494_, v_snd_2498_);
v___x_2523_ = lean_unsigned_to_nat(1u);
v___x_2524_ = lean_nat_add(v_snd_2498_, v___x_2523_);
v___x_2525_ = lean_nat_dec_lt(v___x_2524_, v___x_2502_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; 
lean_dec(v___x_2524_);
v___x_2526_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2510_ = v___x_2526_;
goto v___jp_2509_;
}
else
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_array_fget_borrowed(v_chain_2494_, v___x_2524_);
lean_dec(v___x_2524_);
lean_inc(v___x_2527_);
v___y_2510_ = v___x_2527_;
goto v___jp_2509_;
}
v___jp_2509_:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_inc(v___x_2508_);
v___x_2511_ = l_Lean_Fmt_TaggedDoc_nested(v___x_2508_);
v___x_2512_ = lean_unsigned_to_nat(2u);
v___x_2513_ = lean_mk_empty_array_with_capacity(v___x_2512_);
v___x_2514_ = lean_array_push(v___x_2513_, v___x_2511_);
v___x_2515_ = lean_array_push(v___x_2514_, v___y_2510_);
v___x_2516_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2495_, v___x_2515_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = lean_array_push(v_fst_2497_, v___x_2516_);
v___x_2518_ = lean_nat_add(v_snd_2498_, v___x_2512_);
lean_dec(v_snd_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v___x_2518_);
lean_ctor_set(v___x_2500_, 0, v___x_2517_);
v___x_2520_ = v___x_2500_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
v_a_2496_ = v___x_2520_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object* v_chain_2529_, lean_object* v_format_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2529_, v_format_2530_, v_a_2531_);
lean_dec_ref(v_format_2530_);
lean_dec_ref(v_chain_2529_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object* v_format_2533_, lean_object* v_chain_2534_, uint8_t v_isHeadless_2535_){
_start:
{
lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2543_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2553_; lean_object* v___x_2556_; uint8_t v___y_2558_; uint8_t v_trailingOperator_2571_; 
v___x_2556_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2571_ = lean_ctor_get_uint8(v_format_2533_, 1);
v___y_2558_ = v_trailingOperator_2571_;
goto v___jp_2557_;
v___jp_2536_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_fst_2541_; 
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___y_2537_);
lean_ctor_set(v___x_2539_, 1, v___y_2538_);
v___x_2540_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2534_, v_format_2533_, v___x_2539_);
v_fst_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_fst_2541_);
lean_dec_ref(v___x_2540_);
return v_fst_2541_;
}
v___jp_2542_:
{
if (v_isHeadless_2535_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_unsigned_to_nat(0u);
v___y_2537_ = v___y_2543_;
v___y_2538_ = v___x_2544_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_unsigned_to_nat(1u);
v___y_2537_ = v___y_2543_;
v___y_2538_ = v___x_2545_;
goto v___jp_2536_;
}
}
v___jp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_fst_2551_; 
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___y_2547_);
lean_ctor_set(v___x_2549_, 1, v___y_2548_);
v___x_2550_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2534_, v_format_2533_, v___x_2549_);
v_fst_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_fst_2551_);
lean_dec_ref(v___x_2550_);
return v_fst_2551_;
}
v___jp_2552_:
{
if (v_isHeadless_2535_ == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v___y_2547_ = v___y_2553_;
v___y_2548_ = v___x_2554_;
goto v___jp_2546_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_unsigned_to_nat(0u);
v___y_2547_ = v___y_2553_;
v___y_2548_ = v___x_2555_;
goto v___jp_2546_;
}
}
v___jp_2557_:
{
if (v___y_2558_ == 0)
{
if (v_isHeadless_2535_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_array_get_borrowed(v___x_2556_, v_chain_2534_, v___x_2559_);
v___x_2561_ = lean_unsigned_to_nat(1u);
v___x_2562_ = lean_mk_empty_array_with_capacity(v___x_2561_);
lean_inc(v___x_2560_);
v___x_2563_ = lean_array_push(v___x_2562_, v___x_2560_);
v___y_2553_ = v___x_2563_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2553_ = v___x_2564_;
goto v___jp_2552_;
}
}
else
{
if (v_isHeadless_2535_ == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2543_ = v___x_2565_;
goto v___jp_2542_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = lean_array_get_borrowed(v___x_2556_, v_chain_2534_, v___x_2566_);
v___x_2568_ = lean_unsigned_to_nat(1u);
v___x_2569_ = lean_mk_empty_array_with_capacity(v___x_2568_);
lean_inc(v___x_2567_);
v___x_2570_ = lean_array_push(v___x_2569_, v___x_2567_);
v___y_2543_ = v___x_2570_;
goto v___jp_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object* v_format_2572_, lean_object* v_chain_2573_, lean_object* v_isHeadless_2574_){
_start:
{
uint8_t v_isHeadless_boxed_2575_; lean_object* v_res_2576_; 
v_isHeadless_boxed_2575_ = lean_unbox(v_isHeadless_2574_);
v_res_2576_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2572_, v_chain_2573_, v_isHeadless_boxed_2575_);
lean_dec_ref(v_chain_2573_);
lean_dec_ref(v_format_2572_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object* v_chain_2577_, lean_object* v_format_2578_, lean_object* v_inst_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2577_, v_format_2578_, v_a_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object* v_chain_2582_, lean_object* v_format_2583_, lean_object* v_inst_2584_, lean_object* v_a_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(v_chain_2582_, v_format_2583_, v_inst_2584_, v_a_2585_);
lean_dec_ref(v_format_2583_);
lean_dec_ref(v_chain_2582_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object* v_chain_2587_, lean_object* v_format_2588_, lean_object* v_inst_2589_, lean_object* v_a_2590_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2587_, v_format_2588_, v_a_2590_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object* v_chain_2592_, lean_object* v_format_2593_, lean_object* v_inst_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(v_chain_2592_, v_format_2593_, v_inst_2594_, v_a_2595_);
lean_dec_ref(v_format_2593_);
lean_dec_ref(v_chain_2592_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object* v_format_2597_, lean_object* v_docs_2598_){
_start:
{
uint8_t v___y_2600_; uint8_t v___x_2603_; 
v___x_2603_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_format_2597_);
if (v___x_2603_ == 0)
{
uint8_t v___x_2604_; 
v___x_2604_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_format_2597_);
if (v___x_2604_ == 0)
{
uint8_t v_spacing_2605_; 
v_spacing_2605_ = lean_ctor_get_uint8(v_format_2597_, 2);
v___y_2600_ = v_spacing_2605_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2606_; uint8_t v___y_2608_; uint8_t v_spacing_2635_; 
v___x_2606_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_spacing_2635_ = lean_ctor_get_uint8(v_format_2597_, 2);
v___y_2608_ = v_spacing_2635_;
goto v___jp_2607_;
v___jp_2607_:
{
if (v___y_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_array_get_size(v_docs_2598_);
v___x_2611_ = lean_unsigned_to_nat(1u);
v___x_2612_ = lean_nat_sub(v___x_2610_, v___x_2611_);
lean_inc(v___x_2612_);
lean_inc_ref(v_docs_2598_);
v___x_2613_ = l_Array_toSubarray___redArg(v_docs_2598_, v___x_2609_, v___x_2612_);
v___x_2614_ = l_Subarray_copy___redArg(v___x_2613_);
v___x_2615_ = l_Lean_Fmt_TaggedDoc_fill(v___x_2614_);
v___x_2616_ = lean_array_get(v___x_2606_, v_docs_2598_, v___x_2612_);
lean_dec(v___x_2612_);
lean_dec_ref(v_docs_2598_);
v___x_2617_ = lean_unsigned_to_nat(2u);
v___x_2618_ = lean_mk_empty_array_with_capacity(v___x_2617_);
v___x_2619_ = lean_array_push(v___x_2618_, v___x_2615_);
v___x_2620_ = lean_array_push(v___x_2619_, v___x_2616_);
v___x_2621_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2620_, v___y_2608_);
lean_dec_ref(v___x_2620_);
return v___x_2621_;
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_array_get_size(v_docs_2598_);
v___x_2624_ = lean_unsigned_to_nat(1u);
v___x_2625_ = lean_nat_sub(v___x_2623_, v___x_2624_);
lean_inc(v___x_2625_);
lean_inc_ref(v_docs_2598_);
v___x_2626_ = l_Array_toSubarray___redArg(v_docs_2598_, v___x_2622_, v___x_2625_);
v___x_2627_ = l_Subarray_copy___redArg(v___x_2626_);
v___x_2628_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_2627_);
v___x_2629_ = lean_array_get(v___x_2606_, v_docs_2598_, v___x_2625_);
lean_dec(v___x_2625_);
lean_dec_ref(v_docs_2598_);
v___x_2630_ = lean_unsigned_to_nat(2u);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2632_ = lean_array_push(v___x_2631_, v___x_2628_);
v___x_2633_ = lean_array_push(v___x_2632_, v___x_2629_);
v___x_2634_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2633_, v___x_2604_);
lean_dec_ref(v___x_2633_);
return v___x_2634_;
}
}
}
}
else
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Fmt_Layouts_lines(v_docs_2598_);
lean_dec_ref(v_docs_2598_);
return v___x_2636_;
}
v___jp_2599_:
{
if (v___y_2600_ == 0)
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_Fmt_TaggedDoc_fill(v_docs_2598_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v_docs_2598_);
return v___x_2602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object* v_format_2637_, lean_object* v_docs_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2637_, v_docs_2638_);
lean_dec_ref(v_format_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object* v_columnPos_2640_, lean_object* v_indentation_2641_, lean_object* v_nonCumulativeIndentation_2642_){
_start:
{
lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2643_ = lean_nat_add(v_indentation_2641_, v_nonCumulativeIndentation_2642_);
v___x_2644_ = lean_nat_dec_le(v_columnPos_2640_, v___x_2643_);
lean_dec(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object* v_columnPos_2645_, lean_object* v_indentation_2646_, lean_object* v_nonCumulativeIndentation_2647_){
_start:
{
uint8_t v_res_2648_; lean_object* v_r_2649_; 
v_res_2648_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(v_columnPos_2645_, v_indentation_2646_, v_nonCumulativeIndentation_2647_);
lean_dec(v_nonCumulativeIndentation_2647_);
lean_dec(v_indentation_2646_);
lean_dec(v_columnPos_2645_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object* v_format_2666_, lean_object* v_combinedChain_2667_){
_start:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v_firstOperand_2670_; lean_object* v___y_2672_; uint8_t v___y_2692_; uint8_t v_hardNestedFirstOperand_2699_; 
v___x_2668_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2669_ = lean_unsigned_to_nat(0u);
v_firstOperand_2670_ = lean_array_get_borrowed(v___x_2668_, v_combinedChain_2667_, v___x_2669_);
v_hardNestedFirstOperand_2699_ = lean_ctor_get_uint8(v_format_2666_, 0);
v___y_2692_ = v_hardNestedFirstOperand_2699_;
goto v___jp_2691_;
v___jp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v_compactFirstOperation_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v_compactedChain_2686_; lean_object* v___x_2687_; 
v___x_2673_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion));
v___x_2674_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2673_, v___y_2672_);
v___x_2675_ = lean_unsigned_to_nat(2u);
v___x_2676_ = lean_mk_empty_array_with_capacity(v___x_2675_);
lean_inc(v_firstOperand_2670_);
v___x_2677_ = lean_array_push(v___x_2676_, v_firstOperand_2670_);
v___x_2678_ = lean_array_push(v___x_2677_, v___x_2674_);
v_compactFirstOperation_2679_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2666_, v___x_2678_);
lean_dec_ref(v___x_2678_);
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_mk_empty_array_with_capacity(v___x_2680_);
v___x_2682_ = lean_array_push(v___x_2681_, v_compactFirstOperation_2679_);
v___x_2683_ = lean_array_get_size(v_combinedChain_2667_);
v___x_2684_ = l_Array_toSubarray___redArg(v_combinedChain_2667_, v___x_2675_, v___x_2683_);
v___x_2685_ = l_Subarray_copy___redArg(v___x_2684_);
v_compactedChain_2686_ = l_Array_append___redArg(v___x_2682_, v___x_2685_);
lean_dec_ref(v___x_2685_);
v___x_2687_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2666_, v_compactedChain_2686_);
return v___x_2687_;
}
v___jp_2688_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_unsigned_to_nat(1u);
v___x_2690_ = lean_array_get_borrowed(v___x_2668_, v_combinedChain_2667_, v___x_2689_);
lean_inc(v___x_2690_);
v___y_2672_ = v___x_2690_;
goto v___jp_2671_;
}
v___jp_2691_:
{
if (v___y_2692_ == 0)
{
goto v___jp_2688_;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2693_ = lean_unsigned_to_nat(2u);
v___x_2694_ = lean_array_get_size(v_combinedChain_2667_);
v___x_2695_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
goto v___jp_2688_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_array_get_borrowed(v___x_2668_, v_combinedChain_2667_, v___x_2696_);
lean_inc(v___x_2697_);
v___x_2698_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2697_);
v___y_2672_ = v___x_2698_;
goto v___jp_2671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object* v_format_2700_, lean_object* v_combinedChain_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2700_, v_combinedChain_2701_);
lean_dec_ref(v_format_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object* v_format_2703_, lean_object* v_docs_2704_, lean_object* v_wrap_2705_){
_start:
{
uint8_t v___y_2707_; uint8_t v_spacing_2710_; 
v_spacing_2710_ = lean_ctor_get_uint8(v_format_2703_, 2);
v___y_2707_ = v_spacing_2710_;
goto v___jp_2706_;
v___jp_2706_:
{
if (v___y_2707_ == 0)
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_Fmt_TaggedDoc_fillWrapping(v_docs_2704_, v_wrap_2705_);
return v___x_2708_;
}
else
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(v_docs_2704_, v_wrap_2705_);
return v___x_2709_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object* v_format_2711_, lean_object* v_docs_2712_, lean_object* v_wrap_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2711_, v_docs_2712_, v_wrap_2713_);
lean_dec_ref(v_format_2711_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object* v___x_2715_, size_t v_sz_2716_, size_t v_i_2717_, lean_object* v_bs_2718_){
_start:
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_usize_dec_lt(v_i_2717_, v_sz_2716_);
if (v___x_2719_ == 0)
{
return v_bs_2718_;
}
else
{
lean_object* v___x_2720_; lean_object* v_v_2721_; lean_object* v___x_2722_; lean_object* v_bs_x27_2723_; lean_object* v___y_2725_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2720_ = lean_unsigned_to_nat(1u);
v_v_2721_ = lean_array_uget(v_bs_2718_, v_i_2717_);
v___x_2722_ = lean_unsigned_to_nat(0u);
v_bs_x27_2723_ = lean_array_uset(v_bs_2718_, v_i_2717_, v___x_2722_);
v___x_2730_ = lean_usize_to_nat(v_i_2717_);
v___x_2731_ = lean_nat_sub(v___x_2715_, v___x_2720_);
v___x_2732_ = lean_nat_dec_lt(v___x_2730_, v___x_2731_);
lean_dec(v___x_2731_);
lean_dec(v___x_2730_);
if (v___x_2732_ == 0)
{
v___y_2725_ = v_v_2721_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2721_);
v___y_2725_ = v___x_2733_;
goto v___jp_2724_;
}
v___jp_2724_:
{
size_t v___x_2726_; size_t v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = ((size_t)1ULL);
v___x_2727_ = lean_usize_add(v_i_2717_, v___x_2726_);
v___x_2728_ = lean_array_uset(v_bs_x27_2723_, v_i_2717_, v___y_2725_);
v_i_2717_ = v___x_2727_;
v_bs_2718_ = v___x_2728_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object* v___x_2734_, lean_object* v_sz_2735_, lean_object* v_i_2736_, lean_object* v_bs_2737_){
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2735_);
lean_dec(v_sz_2735_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2736_);
lean_dec(v_i_2736_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2734_, v_sz_boxed_2738_, v_i_boxed_2739_, v_bs_2737_);
lean_dec(v___x_2734_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object* v_chain_2755_, lean_object* v_format_2756_){
_start:
{
uint8_t v___y_2758_; lean_object* v_doc_2759_; lean_object* v___x_2763_; lean_object* v_snd_2764_; lean_object* v_fst_2765_; lean_object* v_fst_2766_; lean_object* v_snd_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2763_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2756_, v_chain_2755_);
v_snd_2764_ = lean_ctor_get(v___x_2763_, 1);
lean_inc(v_snd_2764_);
v_fst_2765_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_fst_2765_);
lean_dec_ref(v___x_2763_);
v_fst_2766_ = lean_ctor_get(v_snd_2764_, 0);
lean_inc(v_fst_2766_);
v_snd_2767_ = lean_ctor_get(v_snd_2764_, 1);
lean_inc(v_snd_2767_);
lean_dec(v_snd_2764_);
v___x_2768_ = lean_array_get_size(v_fst_2765_);
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = lean_nat_dec_eq(v___x_2768_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; uint8_t v___x_2772_; lean_object* v_combinedChain_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___y_2777_; lean_object* v___y_2778_; lean_object* v_doc_2779_; lean_object* v___y_2794_; uint8_t v___y_2795_; lean_object* v___y_2796_; uint8_t v___x_2803_; uint8_t v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2810_; uint8_t v___y_2811_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v_combinedChain_2820_; uint8_t v___y_2823_; uint8_t v___y_2830_; uint8_t v___y_2831_; uint8_t v___y_2839_; uint8_t v___y_2842_; 
v___x_2771_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2772_ = lean_unbox(v_fst_2766_);
v_combinedChain_2773_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2756_, v_fst_2765_, v___x_2772_);
v___x_2774_ = lean_array_get_size(v_combinedChain_2773_);
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2803_ = lean_nat_dec_eq(v___x_2774_, v___x_2775_);
if (v___x_2803_ == 0)
{
uint8_t v_trailingOperator_2843_; 
v_trailingOperator_2843_ = lean_ctor_get_uint8(v_format_2756_, 1);
v___y_2842_ = v_trailingOperator_2843_;
goto v___jp_2841_;
}
else
{
lean_object* v___x_2844_; 
lean_dec(v_snd_2767_);
lean_dec(v_fst_2766_);
lean_dec(v_fst_2765_);
v___x_2844_ = lean_array_get(v___x_2771_, v_combinedChain_2773_, v___x_2769_);
lean_dec_ref(v_combinedChain_2773_);
return v___x_2844_;
}
v___jp_2776_:
{
lean_object* v___x_2780_; lean_object* v_lastOperand_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; lean_object* v___x_2784_; 
v___x_2780_ = lean_nat_sub(v___x_2768_, v___x_2775_);
v_lastOperand_2781_ = lean_array_get(v___x_2771_, v_fst_2765_, v___x_2780_);
lean_dec(v___x_2780_);
lean_dec(v_fst_2765_);
v___x_2782_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
v___x_2783_ = lean_unbox(v_snd_2767_);
lean_inc_ref(v___y_2778_);
lean_inc(v_lastOperand_2781_);
lean_inc_ref(v_doc_2779_);
v___x_2784_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2756_, v_doc_2779_, v_lastOperand_2781_, v___x_2783_, v___y_2778_, v___x_2782_);
if (lean_obj_tag(v___x_2784_) == 1)
{
lean_object* v_val_2785_; 
lean_dec(v_lastOperand_2781_);
lean_dec_ref(v_doc_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v_snd_2767_);
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___y_2758_ = v___y_2777_;
v_doc_2759_ = v_val_2785_;
goto v___jp_2757_;
}
else
{
uint8_t v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v___x_2784_);
v___x_2786_ = lean_unbox(v_snd_2767_);
lean_inc_ref(v___y_2778_);
lean_inc(v_lastOperand_2781_);
lean_inc_ref(v_doc_2779_);
v___x_2787_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2756_, v_doc_2779_, v_lastOperand_2781_, v___x_2786_, v___y_2778_);
if (lean_obj_tag(v___x_2787_) == 1)
{
lean_object* v_val_2788_; 
lean_dec(v_lastOperand_2781_);
lean_dec_ref(v_doc_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v_snd_2767_);
v_val_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_val_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___y_2758_ = v___y_2777_;
v_doc_2759_ = v_val_2788_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2789_; uint8_t v___x_2790_; lean_object* v___x_2791_; 
lean_dec(v___x_2787_);
v___x_2789_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
v___x_2790_ = lean_unbox(v_snd_2767_);
lean_dec(v_snd_2767_);
lean_inc_ref(v_doc_2779_);
v___x_2791_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2756_, v_doc_2779_, v_lastOperand_2781_, v___x_2790_, v___y_2778_, v___x_2789_);
if (lean_obj_tag(v___x_2791_) == 1)
{
lean_object* v_val_2792_; 
lean_dec_ref(v_doc_2779_);
v_val_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_val_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___y_2758_ = v___y_2777_;
v_doc_2759_ = v_val_2792_;
goto v___jp_2757_;
}
else
{
lean_dec(v___x_2791_);
v___y_2758_ = v___y_2777_;
v_doc_2759_ = v_doc_2779_;
goto v___jp_2757_;
}
}
}
}
v___jp_2793_:
{
if (v___y_2795_ == 0)
{
v___y_2777_ = v___y_2795_;
v___y_2778_ = v___y_2796_;
v_doc_2779_ = v___y_2794_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_doc_2802_; 
lean_inc_ref(v___y_2796_);
v___x_2797_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2756_, v___y_2796_);
v___x_2798_ = lean_unsigned_to_nat(2u);
v___x_2799_ = lean_mk_empty_array_with_capacity(v___x_2798_);
v___x_2800_ = lean_array_push(v___x_2799_, v___x_2797_);
v___x_2801_ = lean_array_push(v___x_2800_, v___y_2794_);
v_doc_2802_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2801_);
v___y_2777_ = v___y_2795_;
v___y_2778_ = v___y_2796_;
v_doc_2779_ = v_doc_2802_;
goto v___jp_2776_;
}
}
v___jp_2804_:
{
uint8_t v___x_2808_; 
v___x_2808_ = lean_unbox(v_fst_2766_);
lean_dec(v_fst_2766_);
if (v___x_2808_ == 0)
{
v___y_2794_ = v___y_2807_;
v___y_2795_ = v___y_2805_;
v___y_2796_ = v___y_2806_;
goto v___jp_2793_;
}
else
{
if (v___x_2803_ == 0)
{
v___y_2777_ = v___y_2805_;
v___y_2778_ = v___y_2806_;
v_doc_2779_ = v___y_2807_;
goto v___jp_2776_;
}
else
{
v___y_2794_ = v___y_2807_;
v___y_2795_ = v___y_2805_;
v___y_2796_ = v___y_2806_;
goto v___jp_2793_;
}
}
}
v___jp_2809_:
{
lean_object* v___x_2812_; 
lean_inc_ref(v___y_2810_);
v___x_2812_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2756_, v___y_2810_);
v___y_2805_ = v___y_2811_;
v___y_2806_ = v___y_2810_;
v___y_2807_ = v___x_2812_;
goto v___jp_2804_;
}
v___jp_2813_:
{
if (v___y_2815_ == 0)
{
uint8_t v___x_2816_; 
v___x_2816_ = 1;
v___y_2810_ = v___y_2814_;
v___y_2811_ = v___x_2816_;
goto v___jp_2809_;
}
else
{
if (v___x_2803_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
lean_inc_ref(v___y_2814_);
v___x_2818_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2756_, v___y_2814_, v___x_2817_);
v___y_2805_ = v___x_2803_;
v___y_2806_ = v___y_2814_;
v___y_2807_ = v___x_2818_;
goto v___jp_2804_;
}
else
{
v___y_2810_ = v___y_2814_;
v___y_2811_ = v___x_2803_;
goto v___jp_2809_;
}
}
}
v___jp_2819_:
{
uint8_t v_trailingOperator_2821_; 
v_trailingOperator_2821_ = lean_ctor_get_uint8(v_format_2756_, 1);
v___y_2814_ = v_combinedChain_2820_;
v___y_2815_ = v_trailingOperator_2821_;
goto v___jp_2813_;
}
v___jp_2822_:
{
if (v___y_2823_ == 0)
{
v_combinedChain_2820_ = v_combinedChain_2773_;
goto v___jp_2819_;
}
else
{
size_t v_sz_2824_; size_t v___x_2825_; lean_object* v_combinedChain_2826_; 
v_sz_2824_ = lean_array_size(v_combinedChain_2773_);
v___x_2825_ = ((size_t)0ULL);
v_combinedChain_2826_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2774_, v_sz_2824_, v___x_2825_, v_combinedChain_2773_);
v_combinedChain_2820_ = v_combinedChain_2826_;
goto v___jp_2819_;
}
}
v___jp_2827_:
{
uint8_t v_hardNestedFirstOperand_2828_; 
v_hardNestedFirstOperand_2828_ = lean_ctor_get_uint8(v_format_2756_, 0);
v___y_2823_ = v_hardNestedFirstOperand_2828_;
goto v___jp_2822_;
}
v___jp_2829_:
{
if (v___y_2831_ == 0)
{
if (v___y_2830_ == 0)
{
v_combinedChain_2820_ = v_combinedChain_2773_;
goto v___jp_2819_;
}
else
{
goto v___jp_2827_;
}
}
else
{
uint8_t v___x_2832_; 
v___x_2832_ = lean_nat_dec_lt(v___x_2769_, v___x_2774_);
if (v___x_2832_ == 0)
{
v_combinedChain_2820_ = v_combinedChain_2773_;
goto v___jp_2819_;
}
else
{
lean_object* v_v_2833_; lean_object* v___x_2834_; lean_object* v_xs_x27_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_v_2833_ = lean_array_fget(v_combinedChain_2773_, v___x_2769_);
v___x_2834_ = lean_box(0);
v_xs_x27_2835_ = lean_array_fset(v_combinedChain_2773_, v___x_2769_, v___x_2834_);
v___x_2836_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2833_);
v___x_2837_ = lean_array_fset(v_xs_x27_2835_, v___x_2769_, v___x_2836_);
v_combinedChain_2820_ = v___x_2837_;
goto v___jp_2819_;
}
}
}
v___jp_2838_:
{
uint8_t v_hardNestedFirstOperand_2840_; 
v_hardNestedFirstOperand_2840_ = lean_ctor_get_uint8(v_format_2756_, 0);
v___y_2830_ = v___y_2839_;
v___y_2831_ = v_hardNestedFirstOperand_2840_;
goto v___jp_2829_;
}
v___jp_2841_:
{
if (v___y_2842_ == 0)
{
v___y_2839_ = v___y_2842_;
goto v___jp_2838_;
}
else
{
if (v___x_2803_ == 0)
{
goto v___jp_2827_;
}
else
{
v___y_2839_ = v___y_2842_;
goto v___jp_2838_;
}
}
}
}
else
{
lean_object* v___x_2845_; 
lean_dec(v_snd_2767_);
lean_dec(v_fst_2766_);
lean_dec(v_fst_2765_);
v___x_2845_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_2845_;
}
v___jp_2757_:
{
if (v___y_2758_ == 0)
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2759_);
return v___x_2760_;
}
else
{
lean_object* v_doc_2761_; lean_object* v___x_2762_; 
v_doc_2761_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2759_);
v___x_2762_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2761_);
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object* v_chain_2846_, lean_object* v_format_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_2846_, v_format_2847_);
lean_dec_ref(v_format_2847_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object* v___x_2849_, lean_object* v_as_2850_, size_t v_sz_2851_, size_t v_i_2852_, lean_object* v_bs_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2849_, v_sz_2851_, v_i_2852_, v_bs_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object* v___x_2855_, lean_object* v_as_2856_, lean_object* v_sz_2857_, lean_object* v_i_2858_, lean_object* v_bs_2859_){
_start:
{
size_t v_sz_boxed_2860_; size_t v_i_boxed_2861_; lean_object* v_res_2862_; 
v_sz_boxed_2860_ = lean_unbox_usize(v_sz_2857_);
lean_dec(v_sz_2857_);
v_i_boxed_2861_ = lean_unbox_usize(v_i_2858_);
lean_dec(v_i_2858_);
v_res_2862_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(v___x_2855_, v_as_2856_, v_sz_boxed_2860_, v_i_boxed_2861_, v_bs_2859_);
lean_dec_ref(v_as_2856_);
lean_dec(v___x_2855_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object* v_lhs_2863_, lean_object* v_typeAscriptionTk_2864_, lean_object* v_rhs_2865_, lean_object* v_format_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2867_ = lean_unsigned_to_nat(3u);
v___x_2868_ = lean_mk_empty_array_with_capacity(v___x_2867_);
v___x_2869_ = lean_array_push(v___x_2868_, v_lhs_2863_);
v___x_2870_ = lean_array_push(v___x_2869_, v_typeAscriptionTk_2864_);
v___x_2871_ = lean_array_push(v___x_2870_, v_rhs_2865_);
v___x_2872_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2871_, v_format_2866_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object* v_lhs_2873_, lean_object* v_typeAscriptionTk_2874_, lean_object* v_rhs_2875_, lean_object* v_format_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_Fmt_Layouts_typeAscription(v_lhs_2873_, v_typeAscriptionTk_2874_, v_rhs_2875_, v_format_2876_);
lean_dec_ref(v_format_2876_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(lean_object* v_x_2878_){
_start:
{
if (lean_obj_tag(v_x_2878_) == 0)
{
lean_object* v___x_2879_; 
v___x_2879_ = lean_unsigned_to_nat(0u);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; 
v___x_2880_ = lean_unsigned_to_nat(1u);
return v___x_2880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___boxed(lean_object* v_x_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(v_x_2881_);
lean_dec_ref(v_x_2881_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object* v_t_2883_, lean_object* v_k_2884_){
_start:
{
if (lean_obj_tag(v_t_2883_) == 0)
{
uint8_t v_spacing_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_spacing_2885_ = lean_ctor_get_uint8(v_t_2883_, 0);
lean_dec_ref_known(v_t_2883_, 0);
v___x_2886_ = lean_box(v_spacing_2885_);
v___x_2887_ = lean_apply_1(v_k_2884_, v___x_2886_);
return v___x_2887_;
}
else
{
lean_object* v_sep_2888_; uint8_t v_unindentedRb_2889_; uint8_t v_stickynessKind_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_sep_2888_ = lean_ctor_get(v_t_2883_, 0);
lean_inc_ref(v_sep_2888_);
v_unindentedRb_2889_ = lean_ctor_get_uint8(v_t_2883_, sizeof(void*)*1);
v_stickynessKind_2890_ = lean_ctor_get_uint8(v_t_2883_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_2883_, 1);
v___x_2891_ = lean_box(v_unindentedRb_2889_);
v___x_2892_ = lean_box(v_stickynessKind_2890_);
v___x_2893_ = lean_apply_3(v_k_2884_, v_sep_2888_, v___x_2891_, v___x_2892_);
return v___x_2893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object* v_motive_2894_, lean_object* v_ctorIdx_2895_, lean_object* v_t_2896_, lean_object* v_h_2897_, lean_object* v_k_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2896_, v_k_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object* v_motive_2900_, lean_object* v_ctorIdx_2901_, lean_object* v_t_2902_, lean_object* v_h_2903_, lean_object* v_k_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(v_motive_2900_, v_ctorIdx_2901_, v_t_2902_, v_h_2903_, v_k_2904_);
lean_dec(v_ctorIdx_2901_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object* v_t_2906_, lean_object* v_dense_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2906_, v_dense_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object* v_motive_2909_, lean_object* v_t_2910_, lean_object* v_h_2911_, lean_object* v_dense_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2910_, v_dense_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object* v_t_2914_, lean_object* v_sparse_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2914_, v_sparse_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object* v_motive_2917_, lean_object* v_t_2918_, lean_object* v_h_2919_, lean_object* v_sparse_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2918_, v_sparse_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object* v_lb_2922_, lean_object* v_rb_2923_, uint8_t v_isBodyAligned_2924_, uint8_t v_isBodyPseudoAligned_2925_, uint8_t v___x_2926_, lean_object* v_body_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v_doc_2934_; 
v___x_2928_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2927_);
v___x_2929_ = lean_unsigned_to_nat(3u);
v___x_2930_ = lean_mk_empty_array_with_capacity(v___x_2929_);
v___x_2931_ = lean_array_push(v___x_2930_, v_lb_2922_);
v___x_2932_ = lean_array_push(v___x_2931_, v___x_2928_);
v___x_2933_ = lean_array_push(v___x_2932_, v_rb_2923_);
v_doc_2934_ = l_Lean_Fmt_Layouts_atomic(v___x_2933_);
lean_dec_ref(v___x_2933_);
if (v_isBodyAligned_2924_ == 0)
{
if (v_isBodyPseudoAligned_2925_ == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2934_, v___x_2926_);
return v___x_2935_;
}
else
{
lean_object* v_doc_2936_; lean_object* v___x_2937_; 
v_doc_2936_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2934_);
v___x_2937_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2936_, v___x_2926_);
return v___x_2937_;
}
}
else
{
lean_object* v_doc_2938_; lean_object* v___x_2939_; 
v_doc_2938_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_2934_);
v___x_2939_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2938_, v___x_2926_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object* v_lb_2940_, lean_object* v_rb_2941_, lean_object* v_isBodyAligned_2942_, lean_object* v_isBodyPseudoAligned_2943_, lean_object* v___x_2944_, lean_object* v_body_2945_){
_start:
{
uint8_t v_isBodyAligned_boxed_2946_; uint8_t v_isBodyPseudoAligned_boxed_2947_; uint8_t v___x_590__boxed_2948_; lean_object* v_res_2949_; 
v_isBodyAligned_boxed_2946_ = lean_unbox(v_isBodyAligned_2942_);
v_isBodyPseudoAligned_boxed_2947_ = lean_unbox(v_isBodyPseudoAligned_2943_);
v___x_590__boxed_2948_ = lean_unbox(v___x_2944_);
v_res_2949_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2940_, v_rb_2941_, v_isBodyAligned_boxed_2946_, v_isBodyPseudoAligned_boxed_2947_, v___x_590__boxed_2948_, v_body_2945_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object* v_lb_2953_, lean_object* v_body_2954_, lean_object* v_rb_2955_, lean_object* v_format_2956_){
_start:
{
uint8_t v___x_2957_; 
v___x_2957_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2954_);
if (v___x_2957_ == 0)
{
lean_object* v_doc_2958_; uint8_t v___x_2959_; 
v_doc_2958_ = lean_ctor_get(v_body_2954_, 0);
v___x_2959_ = 1;
if (lean_obj_tag(v_format_2956_) == 0)
{
uint8_t v_spacing_2960_; 
v_spacing_2960_ = lean_ctor_get_uint8(v_format_2956_, 0);
lean_dec_ref_known(v_format_2956_, 0);
if (v_spacing_2960_ == 0)
{
uint8_t v_isBodyAligned_2961_; uint8_t v_isBodyPseudoAligned_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v_f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_inc(v_doc_2958_);
v_isBodyAligned_2961_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2958_);
lean_inc_ref(v_body_2954_);
v_isBodyPseudoAligned_2962_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_body_2954_);
v___x_2963_ = lean_box(v_isBodyAligned_2961_);
v___x_2964_ = lean_box(v_isBodyPseudoAligned_2962_);
v___x_2965_ = lean_box(v___x_2959_);
v_f_2966_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__0___boxed), 6, 5);
lean_closure_set(v_f_2966_, 0, v_lb_2953_);
lean_closure_set(v_f_2966_, 1, v_rb_2955_);
lean_closure_set(v_f_2966_, 2, v___x_2963_);
lean_closure_set(v_f_2966_, 3, v___x_2964_);
lean_closure_set(v_f_2966_, 4, v___x_2965_);
v___x_2967_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__0));
v___x_2968_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_body_2954_, v_f_2966_, v___x_2967_);
return v___x_2968_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2969_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2954_);
v___x_2970_ = lean_unsigned_to_nat(3u);
v___x_2971_ = lean_mk_empty_array_with_capacity(v___x_2970_);
v___x_2972_ = lean_array_push(v___x_2971_, v_lb_2953_);
v___x_2973_ = lean_array_push(v___x_2972_, v___x_2969_);
v___x_2974_ = lean_array_push(v___x_2973_, v_rb_2955_);
v___x_2975_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2974_);
lean_dec_ref(v___x_2974_);
return v___x_2975_;
}
}
else
{
lean_object* v_sep_2976_; uint8_t v_unindentedRb_2977_; uint8_t v_stickynessKind_2978_; lean_object* v_sparse_2980_; lean_object* v___y_2991_; lean_object* v___y_2994_; lean_object* v___y_3006_; lean_object* v___y_3018_; lean_object* v_body_3030_; uint8_t v___x_3031_; 
v_sep_2976_ = lean_ctor_get(v_format_2956_, 0);
lean_inc_ref(v_sep_2976_);
v_unindentedRb_2977_ = lean_ctor_get_uint8(v_format_2956_, sizeof(void*)*1);
v_stickynessKind_2978_ = lean_ctor_get_uint8(v_format_2956_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_format_2956_, 1);
v_body_3030_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_2954_);
v___x_3031_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2976_);
if (v___x_3031_ == 0)
{
uint8_t v___x_3032_; 
v___x_3032_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_3030_);
if (v___x_3032_ == 0)
{
lean_object* v_doc_3033_; lean_object* v_doc_3034_; uint8_t v___x_3035_; 
v_doc_3033_ = lean_ctor_get(v_sep_2976_, 0);
v_doc_3034_ = lean_ctor_get(v_body_3030_, 0);
lean_inc(v_doc_3034_);
lean_dec_ref(v_body_3030_);
v___x_3035_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3033_);
if (v___x_3035_ == 0)
{
uint8_t v___x_3036_; 
v___x_3036_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3034_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_inc(v_doc_3033_);
v___x_3037_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_3033_, v_doc_3034_);
v___x_3038_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3037_);
v___y_3018_ = v___x_3038_;
goto v___jp_3017_;
}
else
{
lean_object* v___x_3039_; 
lean_dec(v_doc_3034_);
lean_inc(v_doc_3033_);
v___x_3039_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3033_);
v___y_3018_ = v___x_3039_;
goto v___jp_3017_;
}
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3034_);
v___y_3018_ = v___x_3040_;
goto v___jp_3017_;
}
}
else
{
lean_dec_ref(v_body_3030_);
lean_inc_ref(v_sep_2976_);
v___y_3018_ = v_sep_2976_;
goto v___jp_3017_;
}
}
else
{
v___y_3018_ = v_body_3030_;
goto v___jp_3017_;
}
v___jp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v_stickyVariant_2987_; lean_object* v_nonStickyVariant_2988_; lean_object* v___x_2989_; 
lean_inc_ref(v_sparse_2980_);
v___x_2981_ = l_Lean_Fmt_TaggedDoc_aligned(v_sparse_2980_);
v___x_2982_ = lean_unsigned_to_nat(2u);
v___x_2983_ = lean_mk_empty_array_with_capacity(v___x_2982_);
v___x_2984_ = lean_array_push(v___x_2983_, v_sparse_2980_);
v___x_2985_ = lean_array_push(v___x_2984_, v___x_2981_);
v___x_2986_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2985_);
v_stickyVariant_2987_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_2986_, v___x_2959_);
lean_inc_ref(v_stickyVariant_2987_);
v_nonStickyVariant_2988_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_stickyVariant_2987_);
v___x_2989_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_2988_, v_stickyVariant_2987_, v_stickynessKind_2978_);
return v___x_2989_;
}
v___jp_2990_:
{
if (v_unindentedRb_2977_ == 0)
{
v_sparse_2980_ = v___y_2991_;
goto v___jp_2979_;
}
else
{
lean_object* v_sparse_2992_; 
v_sparse_2992_ = l_Lean_Fmt_TaggedDoc_unindented(v___y_2991_, v___x_2959_);
v_sparse_2980_ = v_sparse_2992_;
goto v___jp_2979_;
}
}
v___jp_2993_:
{
uint8_t v___x_2995_; 
v___x_2995_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_2994_);
if (v___x_2995_ == 0)
{
uint8_t v___x_2996_; 
v___x_2996_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rb_2955_);
if (v___x_2996_ == 0)
{
lean_object* v_doc_2997_; lean_object* v_doc_2998_; uint8_t v___x_2999_; 
v_doc_2997_ = lean_ctor_get(v___y_2994_, 0);
lean_inc(v_doc_2997_);
lean_dec_ref(v___y_2994_);
v_doc_2998_ = lean_ctor_get(v_rb_2955_, 0);
lean_inc(v_doc_2998_);
lean_dec_ref(v_rb_2955_);
v___x_2999_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2997_);
if (v___x_2999_ == 0)
{
uint8_t v___x_3000_; 
v___x_3000_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_2998_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_2997_, v_doc_2998_);
v___x_3002_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3001_);
v___y_2991_ = v___x_3002_;
goto v___jp_2990_;
}
else
{
lean_object* v___x_3003_; 
lean_dec(v_doc_2998_);
v___x_3003_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2997_);
v___y_2991_ = v___x_3003_;
goto v___jp_2990_;
}
}
else
{
lean_object* v___x_3004_; 
lean_dec(v_doc_2997_);
v___x_3004_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_2998_);
v___y_2991_ = v___x_3004_;
goto v___jp_2990_;
}
}
else
{
lean_dec_ref(v_rb_2955_);
v___y_2991_ = v___y_2994_;
goto v___jp_2990_;
}
}
else
{
lean_dec_ref(v___y_2994_);
v___y_2991_ = v_rb_2955_;
goto v___jp_2990_;
}
}
v___jp_3005_:
{
uint8_t v___x_3007_; 
v___x_3007_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_3006_);
if (v___x_3007_ == 0)
{
uint8_t v___x_3008_; 
v___x_3008_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2976_);
if (v___x_3008_ == 0)
{
lean_object* v_doc_3009_; lean_object* v_doc_3010_; uint8_t v___x_3011_; 
v_doc_3009_ = lean_ctor_get(v___y_3006_, 0);
lean_inc(v_doc_3009_);
lean_dec_ref(v___y_3006_);
v_doc_3010_ = lean_ctor_get(v_sep_2976_, 0);
lean_inc(v_doc_3010_);
lean_dec_ref(v_sep_2976_);
v___x_3011_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3009_);
if (v___x_3011_ == 0)
{
uint8_t v___x_3012_; 
v___x_3012_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3010_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_3009_, v_doc_3010_);
v___x_3014_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3013_);
v___y_2994_ = v___x_3014_;
goto v___jp_2993_;
}
else
{
lean_object* v___x_3015_; 
lean_dec(v_doc_3010_);
v___x_3015_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3009_);
v___y_2994_ = v___x_3015_;
goto v___jp_2993_;
}
}
else
{
lean_object* v___x_3016_; 
lean_dec(v_doc_3009_);
v___x_3016_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3010_);
v___y_2994_ = v___x_3016_;
goto v___jp_2993_;
}
}
else
{
lean_dec_ref(v_sep_2976_);
v___y_2994_ = v___y_3006_;
goto v___jp_2993_;
}
}
else
{
lean_dec_ref(v___y_3006_);
v___y_2994_ = v_sep_2976_;
goto v___jp_2993_;
}
}
v___jp_3017_:
{
lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3019_ = l_Lean_Fmt_TaggedDoc_hardNested(v___y_3018_);
v___x_3020_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_lb_2953_);
if (v___x_3020_ == 0)
{
uint8_t v___x_3021_; 
v___x_3021_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_3019_);
if (v___x_3021_ == 0)
{
lean_object* v_doc_3022_; lean_object* v_doc_3023_; uint8_t v___x_3024_; 
v_doc_3022_ = lean_ctor_get(v_lb_2953_, 0);
lean_inc(v_doc_3022_);
lean_dec_ref(v_lb_2953_);
v_doc_3023_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_doc_3023_);
lean_dec_ref(v___x_3019_);
v___x_3024_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3022_);
if (v___x_3024_ == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3023_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3026_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_3022_, v_doc_3023_);
v___x_3027_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3026_);
v___y_3006_ = v___x_3027_;
goto v___jp_3005_;
}
else
{
lean_object* v___x_3028_; 
lean_dec(v_doc_3023_);
v___x_3028_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3022_);
v___y_3006_ = v___x_3028_;
goto v___jp_3005_;
}
}
else
{
lean_object* v___x_3029_; 
lean_dec(v_doc_3022_);
v___x_3029_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3023_);
v___y_3006_ = v___x_3029_;
goto v___jp_3005_;
}
}
else
{
lean_dec_ref(v___x_3019_);
v___y_3006_ = v_lb_2953_;
goto v___jp_3005_;
}
}
else
{
lean_dec_ref(v_lb_2953_);
v___y_3006_ = v___x_3019_;
goto v___jp_3005_;
}
}
}
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_dec_ref(v_format_2956_);
lean_dec_ref(v_body_2954_);
v___x_3041_ = lean_unsigned_to_nat(2u);
v___x_3042_ = lean_mk_empty_array_with_capacity(v___x_3041_);
v___x_3043_ = lean_array_push(v___x_3042_, v_lb_2953_);
v___x_3044_ = lean_array_push(v___x_3043_, v_rb_2955_);
v___x_3045_ = l_Lean_Fmt_Layouts_atomic(v___x_3044_);
lean_dec_ref(v___x_3044_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object* v_lbTk_3048_, lean_object* v_body_3049_, lean_object* v_rbTk_3050_){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_3052_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_3048_, v_body_3049_, v_rbTk_3050_, v___x_3051_);
return v___x_3052_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0(void){
_start:
{
uint8_t v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3053_ = 1;
v___x_3054_ = 1;
v___x_3055_ = l_Lean_Fmt_TaggedDoc_break;
v___x_3056_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*1, v___x_3054_);
lean_ctor_set_uint8(v___x_3056_, sizeof(void*)*1 + 1, v___x_3053_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object* v_lbTk_3057_, lean_object* v_seq_3058_, lean_object* v_rbTk_3059_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_obj_once(&l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0, &l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0);
v___x_3061_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_3057_, v_seq_3058_, v_rbTk_3059_, v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t v_isComplex_3062_, lean_object* v_subAlts_3063_){
_start:
{
if (v_isComplex_3062_ == 0)
{
uint8_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = 1;
v___x_3065_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_subAlts_3063_, v___x_3064_);
return v___x_3065_;
}
else
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Fmt_Layouts_lines(v_subAlts_3063_);
return v___x_3066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object* v_isComplex_3067_, lean_object* v_subAlts_3068_){
_start:
{
uint8_t v_isComplex_boxed_3069_; lean_object* v_res_3070_; 
v_isComplex_boxed_3069_ = lean_unbox(v_isComplex_3067_);
v_res_3070_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_boxed_3069_, v_subAlts_3068_);
lean_dec_ref(v_subAlts_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t v_sz_3071_, size_t v_i_3072_, lean_object* v_bs_3073_){
_start:
{
uint8_t v___x_3074_; 
v___x_3074_ = lean_usize_dec_lt(v_i_3072_, v_sz_3071_);
if (v___x_3074_ == 0)
{
return v_bs_3073_;
}
else
{
lean_object* v_v_3075_; lean_object* v___x_3076_; lean_object* v_bs_x27_3077_; lean_object* v___x_3078_; size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v_v_3075_ = lean_array_uget(v_bs_3073_, v_i_3072_);
v___x_3076_ = lean_unsigned_to_nat(0u);
v_bs_x27_3077_ = lean_array_uset(v_bs_3073_, v_i_3072_, v___x_3076_);
v___x_3078_ = l_Lean_Fmt_TaggedDoc_nested(v_v_3075_);
v___x_3079_ = ((size_t)1ULL);
v___x_3080_ = lean_usize_add(v_i_3072_, v___x_3079_);
v___x_3081_ = lean_array_uset(v_bs_x27_3077_, v_i_3072_, v___x_3078_);
v_i_3072_ = v___x_3080_;
v_bs_3073_ = v___x_3081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object* v_sz_3083_, lean_object* v_i_3084_, lean_object* v_bs_3085_){
_start:
{
size_t v_sz_boxed_3086_; size_t v_i_boxed_3087_; lean_object* v_res_3088_; 
v_sz_boxed_3086_ = lean_unbox_usize(v_sz_3083_);
lean_dec(v_sz_3083_);
v_i_boxed_3087_ = lean_unbox_usize(v_i_3084_);
lean_dec(v_i_3084_);
v_res_3088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_boxed_3086_, v_i_boxed_3087_, v_bs_3085_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object* v_subAlts_3089_, lean_object* v_arrowTk_3090_, lean_object* v_rhs_3091_, uint8_t v_isComplex_3092_){
_start:
{
lean_object* v___y_3094_; uint8_t v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3136_; uint8_t v___x_3153_; 
v___x_3153_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_arrowTk_3090_);
if (v___x_3153_ == 0)
{
v___y_3136_ = v___x_3153_;
goto v___jp_3135_;
}
else
{
uint8_t v___x_3154_; 
v___x_3154_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_3091_);
v___y_3136_ = v___x_3154_;
goto v___jp_3135_;
}
v___jp_3093_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v_lhs_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v_nonStickyDoc_3112_; lean_object* v_flat_3113_; lean_object* v___x_3114_; 
v___x_3097_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_3092_, v___y_3096_);
lean_dec_ref(v___y_3096_);
v___x_3098_ = lean_unsigned_to_nat(2u);
v___x_3099_ = lean_mk_empty_array_with_capacity(v___x_3098_);
lean_inc_ref_n(v___x_3099_, 2);
v___x_3100_ = lean_array_push(v___x_3099_, v___x_3097_);
v___x_3101_ = lean_array_push(v___x_3100_, v_arrowTk_3090_);
v_lhs_3102_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3101_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_lhs_3102_);
v___x_3104_ = l_Lean_Fmt_TaggedDoc_nl;
lean_inc_ref(v___y_3094_);
v___x_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v___y_3094_);
lean_inc_ref(v___x_3103_);
v___x_3106_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3103_, v___x_3105_);
v___x_3107_ = lean_box(0);
lean_inc_ref(v_rhs_3091_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v_rhs_3091_);
v___x_3109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
lean_ctor_set(v___x_3109_, 2, v___x_3107_);
v___x_3110_ = lean_array_push(v___x_3099_, v___x_3106_);
v___x_3111_ = lean_array_push(v___x_3110_, v___x_3109_);
v_nonStickyDoc_3112_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3111_);
lean_dec_ref(v___x_3111_);
lean_inc_ref(v_nonStickyDoc_3112_);
v_flat_3113_ = l_Lean_Fmt_TaggedDoc_flattened(v_nonStickyDoc_3112_);
v___x_3114_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_3091_);
if (lean_obj_tag(v___x_3114_) == 1)
{
lean_object* v_val_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3133_; 
v_val_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3133_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_val_3115_);
lean_dec(v___x_3114_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3133_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_stickyVariant_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
v_stickyVariant_3119_ = lean_ctor_get(v_val_3115_, 0);
v___x_3120_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v___y_3094_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
lean_ctor_set(v___x_3121_, 1, v___y_3094_);
v___x_3122_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3103_, v___x_3121_);
lean_inc_ref(v_stickyVariant_3119_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v_stickyVariant_3119_);
v___x_3124_ = v___x_3117_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_stickyVariant_3119_);
v___x_3124_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v_stickyDoc_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3107_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
lean_ctor_set(v___x_3125_, 2, v___x_3107_);
v___x_3126_ = lean_array_push(v___x_3099_, v___x_3122_);
v___x_3127_ = lean_array_push(v___x_3126_, v___x_3125_);
v_stickyDoc_3128_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3127_);
lean_dec_ref(v___x_3127_);
v___x_3129_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_3115_, v___y_3095_);
lean_dec(v_val_3115_);
v___x_3130_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_3112_, v_stickyDoc_3128_, v___x_3129_);
lean_dec(v___x_3129_);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v_flat_3113_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
return v___x_3131_;
}
}
}
else
{
lean_object* v___x_3134_; 
lean_dec(v___x_3114_);
lean_dec_ref_known(v___x_3103_, 1);
lean_dec_ref(v___x_3099_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_flat_3113_);
lean_ctor_set(v___x_3134_, 1, v_nonStickyDoc_3112_);
return v___x_3134_;
}
}
v___jp_3135_:
{
if (v___y_3136_ == 0)
{
lean_object* v___x_3137_; size_t v_sz_3138_; size_t v___x_3139_; lean_object* v_subAlts_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3137_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_sz_3138_ = lean_array_size(v_subAlts_3089_);
v___x_3139_ = ((size_t)0ULL);
v_subAlts_3140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_3138_, v___x_3139_, v_subAlts_3089_);
v___x_3141_ = lean_array_get_size(v_subAlts_3140_);
v___x_3142_ = lean_unsigned_to_nat(1u);
v___x_3143_ = lean_nat_sub(v___x_3141_, v___x_3142_);
v___x_3144_ = lean_nat_dec_lt(v___x_3143_, v___x_3141_);
if (v___x_3144_ == 0)
{
lean_dec(v___x_3143_);
v___y_3094_ = v___x_3137_;
v___y_3095_ = v___y_3136_;
v___y_3096_ = v_subAlts_3140_;
goto v___jp_3093_;
}
else
{
lean_object* v_v_3145_; lean_object* v___x_3146_; lean_object* v_xs_x27_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v_v_3145_ = lean_array_fget(v_subAlts_3140_, v___x_3143_);
v___x_3146_ = lean_box(0);
v_xs_x27_3147_ = lean_array_fset(v_subAlts_3140_, v___x_3143_, v___x_3146_);
v___x_3148_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3145_);
v___x_3149_ = lean_array_fset(v_xs_x27_3147_, v___x_3143_, v___x_3148_);
lean_dec(v___x_3143_);
v___y_3094_ = v___x_3137_;
v___y_3095_ = v___y_3136_;
v___y_3096_ = v___x_3149_;
goto v___jp_3093_;
}
}
else
{
lean_object* v_subAlts_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
lean_dec_ref(v_rhs_3091_);
lean_dec_ref(v_arrowTk_3090_);
v_subAlts_3150_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_3092_, v_subAlts_3089_);
lean_dec_ref(v_subAlts_3089_);
lean_inc_ref(v_subAlts_3150_);
v___x_3151_ = l_Lean_Fmt_TaggedDoc_flattened(v_subAlts_3150_);
v___x_3152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3151_);
lean_ctor_set(v___x_3152_, 1, v_subAlts_3150_);
return v___x_3152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object* v_subAlts_3155_, lean_object* v_arrowTk_3156_, lean_object* v_rhs_3157_, lean_object* v_isComplex_3158_){
_start:
{
uint8_t v_isComplex_boxed_3159_; lean_object* v_res_3160_; 
v_isComplex_boxed_3159_ = lean_unbox(v_isComplex_3158_);
v_res_3160_ = l_Lean_Fmt_Layouts_alt(v_subAlts_3155_, v_arrowTk_3156_, v_rhs_3157_, v_isComplex_boxed_3159_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(size_t v_sz_3161_, size_t v_i_3162_, lean_object* v_bs_3163_){
_start:
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_usize_dec_lt(v_i_3162_, v_sz_3161_);
if (v___x_3164_ == 0)
{
return v_bs_3163_;
}
else
{
lean_object* v_v_3165_; lean_object* v_flat_3166_; lean_object* v___x_3167_; lean_object* v_bs_x27_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v_v_3165_ = lean_array_uget_borrowed(v_bs_3163_, v_i_3162_);
v_flat_3166_ = lean_ctor_get(v_v_3165_, 0);
lean_inc_ref(v_flat_3166_);
v___x_3167_ = lean_unsigned_to_nat(0u);
v_bs_x27_3168_ = lean_array_uset(v_bs_3163_, v_i_3162_, v___x_3167_);
v___x_3169_ = ((size_t)1ULL);
v___x_3170_ = lean_usize_add(v_i_3162_, v___x_3169_);
v___x_3171_ = lean_array_uset(v_bs_x27_3168_, v_i_3162_, v_flat_3166_);
v_i_3162_ = v___x_3170_;
v_bs_3163_ = v___x_3171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object* v_sz_3173_, lean_object* v_i_3174_, lean_object* v_bs_3175_){
_start:
{
size_t v_sz_boxed_3176_; size_t v_i_boxed_3177_; lean_object* v_res_3178_; 
v_sz_boxed_3176_ = lean_unbox_usize(v_sz_3173_);
lean_dec(v_sz_3173_);
v_i_boxed_3177_ = lean_unbox_usize(v_i_3174_);
lean_dec(v_i_3174_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_boxed_3176_, v_i_boxed_3177_, v_bs_3175_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t v_sz_3179_, size_t v_i_3180_, lean_object* v_bs_3181_){
_start:
{
uint8_t v___x_3182_; 
v___x_3182_ = lean_usize_dec_lt(v_i_3180_, v_sz_3179_);
if (v___x_3182_ == 0)
{
return v_bs_3181_;
}
else
{
lean_object* v_v_3183_; lean_object* v_nonFlat_3184_; lean_object* v___x_3185_; lean_object* v_bs_x27_3186_; size_t v___x_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v_v_3183_ = lean_array_uget_borrowed(v_bs_3181_, v_i_3180_);
v_nonFlat_3184_ = lean_ctor_get(v_v_3183_, 1);
lean_inc_ref(v_nonFlat_3184_);
v___x_3185_ = lean_unsigned_to_nat(0u);
v_bs_x27_3186_ = lean_array_uset(v_bs_3181_, v_i_3180_, v___x_3185_);
v___x_3187_ = ((size_t)1ULL);
v___x_3188_ = lean_usize_add(v_i_3180_, v___x_3187_);
v___x_3189_ = lean_array_uset(v_bs_x27_3186_, v_i_3180_, v_nonFlat_3184_);
v_i_3180_ = v___x_3188_;
v_bs_3181_ = v___x_3189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object* v_sz_3191_, lean_object* v_i_3192_, lean_object* v_bs_3193_){
_start:
{
size_t v_sz_boxed_3194_; size_t v_i_boxed_3195_; lean_object* v_res_3196_; 
v_sz_boxed_3194_ = lean_unbox_usize(v_sz_3191_);
lean_dec(v_sz_3191_);
v_i_boxed_3195_ = lean_unbox_usize(v_i_3192_);
lean_dec(v_i_3192_);
v_res_3196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_boxed_3194_, v_i_boxed_3195_, v_bs_3193_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object* v_alts_3197_, uint8_t v_allowFlattenedAlts_3198_){
_start:
{
size_t v_sz_3199_; size_t v___x_3200_; lean_object* v___x_3201_; lean_object* v_unflattened_3202_; 
v_sz_3199_ = lean_array_size(v_alts_3197_);
v___x_3200_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3197_);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_3199_, v___x_3200_, v_alts_3197_);
v_unflattened_3202_ = l_Lean_Fmt_Layouts_lines(v___x_3201_);
lean_dec_ref(v___x_3201_);
if (v_allowFlattenedAlts_3198_ == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v_alts_3197_);
v___x_3203_ = l_Lean_Fmt_TaggedDoc_withPosition(v_unflattened_3202_);
return v___x_3203_;
}
else
{
lean_object* v___x_3204_; lean_object* v_flattened_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_3199_, v___x_3200_, v_alts_3197_);
v_flattened_3205_ = l_Lean_Fmt_Layouts_lines(v___x_3204_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = lean_unsigned_to_nat(2u);
v___x_3207_ = lean_mk_empty_array_with_capacity(v___x_3206_);
v___x_3208_ = lean_array_push(v___x_3207_, v_flattened_3205_);
v___x_3209_ = lean_array_push(v___x_3208_, v_unflattened_3202_);
v___x_3210_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3209_);
v___x_3211_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_3210_);
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object* v_alts_3212_, lean_object* v_allowFlattenedAlts_3213_){
_start:
{
uint8_t v_allowFlattenedAlts_boxed_3214_; lean_object* v_res_3215_; 
v_allowFlattenedAlts_boxed_3214_ = lean_unbox(v_allowFlattenedAlts_3213_);
v_res_3215_ = l_Lean_Fmt_Layouts_alts(v_alts_3212_, v_allowFlattenedAlts_boxed_3214_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(uint8_t v_x_3216_){
_start:
{
if (v_x_3216_ == 0)
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_unsigned_to_nat(0u);
return v___x_3217_;
}
else
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_unsigned_to_nat(1u);
return v___x_3218_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___boxed(lean_object* v_x_3219_){
_start:
{
uint8_t v_x_boxed_3220_; lean_object* v_res_3221_; 
v_x_boxed_3220_ = lean_unbox(v_x_3219_);
v_res_3221_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(v_x_boxed_3220_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object* v_k_3222_){
_start:
{
lean_inc(v_k_3222_);
return v_k_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object* v_k_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(v_k_3223_);
lean_dec(v_k_3223_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object* v_motive_3225_, lean_object* v_ctorIdx_3226_, uint8_t v_t_3227_, lean_object* v_h_3228_, lean_object* v_k_3229_){
_start:
{
lean_inc(v_k_3229_);
return v_k_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object* v_motive_3230_, lean_object* v_ctorIdx_3231_, lean_object* v_t_3232_, lean_object* v_h_3233_, lean_object* v_k_3234_){
_start:
{
uint8_t v_t_boxed_3235_; lean_object* v_res_3236_; 
v_t_boxed_3235_ = lean_unbox(v_t_3232_);
v_res_3236_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(v_motive_3230_, v_ctorIdx_3231_, v_t_boxed_3235_, v_h_3233_, v_k_3234_);
lean_dec(v_k_3234_);
lean_dec(v_ctorIdx_3231_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object* v_sticky_3237_){
_start:
{
lean_inc(v_sticky_3237_);
return v_sticky_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(v_sticky_3238_);
lean_dec(v_sticky_3238_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object* v_motive_3240_, uint8_t v_t_3241_, lean_object* v_h_3242_, lean_object* v_sticky_3243_){
_start:
{
lean_inc(v_sticky_3243_);
return v_sticky_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object* v_motive_3244_, lean_object* v_t_3245_, lean_object* v_h_3246_, lean_object* v_sticky_3247_){
_start:
{
uint8_t v_t_boxed_3248_; lean_object* v_res_3249_; 
v_t_boxed_3248_ = lean_unbox(v_t_3245_);
v_res_3249_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(v_motive_3244_, v_t_boxed_3248_, v_h_3246_, v_sticky_3247_);
lean_dec(v_sticky_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3250_){
_start:
{
lean_inc(v_nonSticky_3250_);
return v_nonSticky_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(v_nonSticky_3251_);
lean_dec(v_nonSticky_3251_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object* v_motive_3253_, uint8_t v_t_3254_, lean_object* v_h_3255_, lean_object* v_nonSticky_3256_){
_start:
{
lean_inc(v_nonSticky_3256_);
return v_nonSticky_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object* v_motive_3257_, lean_object* v_t_3258_, lean_object* v_h_3259_, lean_object* v_nonSticky_3260_){
_start:
{
uint8_t v_t_boxed_3261_; lean_object* v_res_3262_; 
v_t_boxed_3261_ = lean_unbox(v_t_3258_);
v_res_3262_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(v_motive_3257_, v_t_boxed_3261_, v_h_3259_, v_nonSticky_3260_);
lean_dec(v_nonSticky_3260_);
return v_res_3262_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3263_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3264_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___x_3263_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object* v_keywordTk_3266_, lean_object* v_seq_3267_, uint8_t v_format_3268_){
_start:
{
lean_object* v___x_3269_; uint8_t v___x_3270_; lean_object* v_doc_3271_; 
v___x_3269_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3270_ = 1;
v_doc_3271_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_keywordTk_3266_, v___x_3269_, v_seq_3267_, v___x_3270_);
if (v_format_3268_ == 0)
{
lean_object* v___x_3272_; uint8_t v___x_3273_; lean_object* v___x_3274_; 
lean_inc_ref(v_doc_3271_);
v___x_3272_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3271_);
v___x_3273_ = 1;
v___x_3274_ = l_Lean_Fmt_TaggedDoc_sticky(v___x_3272_, v_doc_3271_, v___x_3273_);
return v___x_3274_;
}
else
{
lean_object* v___x_3275_; 
v___x_3275_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3271_);
return v___x_3275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object* v_keywordTk_3276_, lean_object* v_seq_3277_, lean_object* v_format_3278_){
_start:
{
uint8_t v_format_boxed_3279_; lean_object* v_res_3280_; 
v_format_boxed_3279_ = lean_unbox(v_format_3278_);
v_res_3280_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_keywordTk_3276_, v_seq_3277_, v_format_boxed_3279_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(uint8_t v_x_3281_){
_start:
{
if (v_x_3281_ == 0)
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_unsigned_to_nat(0u);
return v___x_3282_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_unsigned_to_nat(1u);
return v___x_3283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___boxed(lean_object* v_x_3284_){
_start:
{
uint8_t v_x_boxed_3285_; lean_object* v_res_3286_; 
v_x_boxed_3285_ = lean_unbox(v_x_3284_);
v_res_3286_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(v_x_boxed_3285_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object* v_k_3287_){
_start:
{
lean_inc(v_k_3287_);
return v_k_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object* v_k_3288_){
_start:
{
lean_object* v_res_3289_; 
v_res_3289_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(v_k_3288_);
lean_dec(v_k_3288_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object* v_motive_3290_, lean_object* v_ctorIdx_3291_, uint8_t v_t_3292_, lean_object* v_h_3293_, lean_object* v_k_3294_){
_start:
{
lean_inc(v_k_3294_);
return v_k_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object* v_motive_3295_, lean_object* v_ctorIdx_3296_, lean_object* v_t_3297_, lean_object* v_h_3298_, lean_object* v_k_3299_){
_start:
{
uint8_t v_t_boxed_3300_; lean_object* v_res_3301_; 
v_t_boxed_3300_ = lean_unbox(v_t_3297_);
v_res_3301_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(v_motive_3295_, v_ctorIdx_3296_, v_t_boxed_3300_, v_h_3298_, v_k_3299_);
lean_dec(v_k_3299_);
lean_dec(v_ctorIdx_3296_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object* v_sticky_3302_){
_start:
{
lean_inc(v_sticky_3302_);
return v_sticky_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(v_sticky_3303_);
lean_dec(v_sticky_3303_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object* v_motive_3305_, uint8_t v_t_3306_, lean_object* v_h_3307_, lean_object* v_sticky_3308_){
_start:
{
lean_inc(v_sticky_3308_);
return v_sticky_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object* v_motive_3309_, lean_object* v_t_3310_, lean_object* v_h_3311_, lean_object* v_sticky_3312_){
_start:
{
uint8_t v_t_boxed_3313_; lean_object* v_res_3314_; 
v_t_boxed_3313_ = lean_unbox(v_t_3310_);
v_res_3314_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(v_motive_3309_, v_t_boxed_3313_, v_h_3311_, v_sticky_3312_);
lean_dec(v_sticky_3312_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3315_){
_start:
{
lean_inc(v_nonSticky_3315_);
return v_nonSticky_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(v_nonSticky_3316_);
lean_dec(v_nonSticky_3316_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object* v_motive_3318_, uint8_t v_t_3319_, lean_object* v_h_3320_, lean_object* v_nonSticky_3321_){
_start:
{
lean_inc(v_nonSticky_3321_);
return v_nonSticky_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object* v_motive_3322_, lean_object* v_t_3323_, lean_object* v_h_3324_, lean_object* v_nonSticky_3325_){
_start:
{
uint8_t v_t_boxed_3326_; lean_object* v_res_3327_; 
v_t_boxed_3326_ = lean_unbox(v_t_3323_);
v_res_3327_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(v_motive_3322_, v_t_boxed_3326_, v_h_3324_, v_nonSticky_3325_);
lean_dec(v_nonSticky_3325_);
return v_res_3327_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3328_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3329_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
lean_ctor_set(v___x_3330_, 1, v___x_3328_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object* v_keyword_3331_, lean_object* v_term_3332_, uint8_t v_format_3333_){
_start:
{
lean_object* v___y_3335_; uint8_t v___x_3350_; 
v___x_3350_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_term_3332_);
if (v___x_3350_ == 0)
{
uint8_t v___x_3351_; lean_object* v___y_3353_; uint8_t v___x_3366_; 
v___x_3351_ = 1;
lean_inc_ref(v_term_3332_);
v___x_3366_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_term_3332_, v___x_3350_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
lean_inc_ref(v_keyword_3331_);
v___x_3367_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3331_);
v___x_3368_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_term_3332_);
v___x_3369_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3367_, v___x_3368_, v_term_3332_, v___x_3351_);
v___x_3370_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3369_);
v___y_3353_ = v___x_3370_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
lean_inc_ref(v_keyword_3331_);
v___x_3371_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3331_);
v___x_3372_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v_term_3332_);
v___x_3373_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3371_, v___x_3372_, v_term_3332_, v___x_3351_);
v___y_3353_ = v___x_3373_;
goto v___jp_3352_;
}
v___jp_3352_:
{
if (v_format_3333_ == 0)
{
lean_object* v___x_3354_; 
lean_inc_ref(v_term_3332_);
v___x_3354_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_term_3332_);
if (lean_obj_tag(v___x_3354_) == 1)
{
lean_object* v_val_3355_; uint8_t v_kind_3356_; 
v_val_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_val_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v_kind_3356_ = lean_ctor_get_uint8(v_val_3355_, sizeof(void*)*1);
lean_dec(v_val_3355_);
if (v_kind_3356_ == 1)
{
v___y_3335_ = v___y_3353_;
goto v___jp_3334_;
}
else
{
if (v___x_3350_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3357_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3331_);
v___x_3358_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3359_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3357_, v___x_3358_, v_term_3332_, v___x_3351_);
v___x_3360_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3353_, v___x_3359_, v_kind_3356_);
return v___x_3360_;
}
else
{
v___y_3335_ = v___y_3353_;
goto v___jp_3334_;
}
}
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; uint8_t v___x_3364_; lean_object* v___x_3365_; 
lean_dec(v___x_3354_);
v___x_3361_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3331_);
v___x_3362_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3363_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3361_, v___x_3362_, v_term_3332_, v___x_3351_);
v___x_3364_ = 0;
v___x_3365_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3353_, v___x_3363_, v___x_3364_);
return v___x_3365_;
}
}
else
{
lean_dec_ref(v_term_3332_);
lean_dec_ref(v_keyword_3331_);
return v___y_3353_;
}
}
}
else
{
uint8_t v___x_3374_; 
lean_dec_ref(v_term_3332_);
v___x_3374_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keyword_3331_);
if (v___x_3374_ == 0)
{
if (v_format_3333_ == 0)
{
lean_object* v___x_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; 
lean_inc_ref(v_keyword_3331_);
v___x_3375_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3331_);
v___x_3376_ = 0;
v___x_3377_ = l_Lean_Fmt_TaggedDoc_sticky(v_keyword_3331_, v___x_3375_, v___x_3376_);
return v___x_3377_;
}
else
{
return v_keyword_3331_;
}
}
else
{
lean_object* v___x_3378_; 
lean_dec_ref(v_keyword_3331_);
v___x_3378_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3378_;
}
}
v___jp_3334_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; 
v___x_3336_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3331_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
v___x_3338_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3339_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3337_, v___x_3338_);
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_term_3332_);
v___x_3342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
lean_ctor_set(v___x_3342_, 2, v___x_3340_);
v___x_3343_ = lean_unsigned_to_nat(2u);
v___x_3344_ = lean_mk_empty_array_with_capacity(v___x_3343_);
v___x_3345_ = lean_array_push(v___x_3344_, v___x_3339_);
v___x_3346_ = lean_array_push(v___x_3345_, v___x_3342_);
v___x_3347_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3346_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = 1;
v___x_3349_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3335_, v___x_3347_, v___x_3348_);
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object* v_keyword_3379_, lean_object* v_term_3380_, lean_object* v_format_3381_){
_start:
{
uint8_t v_format_boxed_3382_; lean_object* v_res_3383_; 
v_format_boxed_3382_ = lean_unbox(v_format_3381_);
v_res_3383_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3379_, v_term_3380_, v_format_boxed_3382_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(uint8_t v_x_3384_){
_start:
{
if (v_x_3384_ == 0)
{
lean_object* v___x_3385_; 
v___x_3385_ = lean_unsigned_to_nat(0u);
return v___x_3385_;
}
else
{
lean_object* v___x_3386_; 
v___x_3386_ = lean_unsigned_to_nat(1u);
return v___x_3386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___boxed(lean_object* v_x_3387_){
_start:
{
uint8_t v_x_boxed_3388_; lean_object* v_res_3389_; 
v_x_boxed_3388_ = lean_unbox(v_x_3387_);
v_res_3389_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(v_x_boxed_3388_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object* v_k_3390_){
_start:
{
lean_inc(v_k_3390_);
return v_k_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object* v_k_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(v_k_3391_);
lean_dec(v_k_3391_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object* v_motive_3393_, lean_object* v_ctorIdx_3394_, uint8_t v_t_3395_, lean_object* v_h_3396_, lean_object* v_k_3397_){
_start:
{
lean_inc(v_k_3397_);
return v_k_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object* v_motive_3398_, lean_object* v_ctorIdx_3399_, lean_object* v_t_3400_, lean_object* v_h_3401_, lean_object* v_k_3402_){
_start:
{
uint8_t v_t_boxed_3403_; lean_object* v_res_3404_; 
v_t_boxed_3403_ = lean_unbox(v_t_3400_);
v_res_3404_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(v_motive_3398_, v_ctorIdx_3399_, v_t_boxed_3403_, v_h_3401_, v_k_3402_);
lean_dec(v_k_3402_);
lean_dec(v_ctorIdx_3399_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object* v_sticky_3405_){
_start:
{
lean_inc(v_sticky_3405_);
return v_sticky_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(v_sticky_3406_);
lean_dec(v_sticky_3406_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object* v_motive_3408_, uint8_t v_t_3409_, lean_object* v_h_3410_, lean_object* v_sticky_3411_){
_start:
{
lean_inc(v_sticky_3411_);
return v_sticky_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object* v_motive_3412_, lean_object* v_t_3413_, lean_object* v_h_3414_, lean_object* v_sticky_3415_){
_start:
{
uint8_t v_t_boxed_3416_; lean_object* v_res_3417_; 
v_t_boxed_3416_ = lean_unbox(v_t_3413_);
v_res_3417_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(v_motive_3412_, v_t_boxed_3416_, v_h_3414_, v_sticky_3415_);
lean_dec(v_sticky_3415_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3418_){
_start:
{
lean_inc(v_nonSticky_3418_);
return v_nonSticky_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(v_nonSticky_3419_);
lean_dec(v_nonSticky_3419_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object* v_motive_3421_, uint8_t v_t_3422_, lean_object* v_h_3423_, lean_object* v_nonSticky_3424_){
_start:
{
lean_inc(v_nonSticky_3424_);
return v_nonSticky_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object* v_motive_3425_, lean_object* v_t_3426_, lean_object* v_h_3427_, lean_object* v_nonSticky_3428_){
_start:
{
uint8_t v_t_boxed_3429_; lean_object* v_res_3430_; 
v_t_boxed_3429_ = lean_unbox(v_t_3426_);
v_res_3430_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(v_motive_3425_, v_t_boxed_3429_, v_h_3427_, v_nonSticky_3428_);
lean_dec(v_nonSticky_3428_);
return v_res_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object* v_keyword_3431_, lean_object* v_alts_3432_, uint8_t v_format_3433_){
_start:
{
uint8_t v___x_3434_; lean_object* v_alts_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v_nonStickyDoc_3440_; 
v___x_3434_ = 1;
v_alts_3435_ = l_Lean_Fmt_Layouts_alts(v_alts_3432_, v___x_3434_);
v___x_3436_ = lean_unsigned_to_nat(2u);
v___x_3437_ = lean_mk_empty_array_with_capacity(v___x_3436_);
lean_inc_ref(v_keyword_3431_);
lean_inc_ref(v___x_3437_);
v___x_3438_ = lean_array_push(v___x_3437_, v_keyword_3431_);
lean_inc_ref(v_alts_3435_);
v___x_3439_ = lean_array_push(v___x_3438_, v_alts_3435_);
v_nonStickyDoc_3440_ = l_Lean_Fmt_Layouts_lines(v___x_3439_);
lean_dec_ref(v___x_3439_);
if (v_format_3433_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v_stickyDoc_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; 
v___x_3441_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3431_);
v___x_3442_ = lean_array_push(v___x_3437_, v___x_3441_);
v___x_3443_ = lean_array_push(v___x_3442_, v_alts_3435_);
v_stickyDoc_3444_ = l_Lean_Fmt_Layouts_lines(v___x_3443_);
lean_dec_ref(v___x_3443_);
v___x_3445_ = 0;
v___x_3446_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3440_, v_stickyDoc_3444_, v___x_3445_);
return v___x_3446_;
}
else
{
lean_dec_ref(v___x_3437_);
lean_dec_ref(v_alts_3435_);
lean_dec_ref(v_keyword_3431_);
return v_nonStickyDoc_3440_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object* v_keyword_3447_, lean_object* v_alts_3448_, lean_object* v_format_3449_){
_start:
{
uint8_t v_format_boxed_3450_; lean_object* v_res_3451_; 
v_format_boxed_3450_ = lean_unbox(v_format_3449_);
v_res_3451_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_keyword_3447_, v_alts_3448_, v_format_boxed_3450_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(lean_object* v_x_3452_){
_start:
{
if (lean_obj_tag(v_x_3452_) == 0)
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_unsigned_to_nat(0u);
return v___x_3453_;
}
else
{
lean_object* v___x_3454_; 
v___x_3454_ = lean_unsigned_to_nat(1u);
return v___x_3454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___boxed(lean_object* v_x_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(v_x_3455_);
lean_dec_ref(v_x_3455_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object* v_t_3457_, lean_object* v_k_3458_){
_start:
{
lean_object* v_sepArrayFormat_3459_; lean_object* v___x_3460_; 
v_sepArrayFormat_3459_ = lean_ctor_get(v_t_3457_, 0);
lean_inc_ref(v_sepArrayFormat_3459_);
lean_dec_ref(v_t_3457_);
v___x_3460_ = lean_apply_1(v_k_3458_, v_sepArrayFormat_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object* v_motive_3461_, lean_object* v_ctorIdx_3462_, lean_object* v_t_3463_, lean_object* v_h_3464_, lean_object* v_k_3465_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3463_, v_k_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object* v_motive_3467_, lean_object* v_ctorIdx_3468_, lean_object* v_t_3469_, lean_object* v_h_3470_, lean_object* v_k_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(v_motive_3467_, v_ctorIdx_3468_, v_t_3469_, v_h_3470_, v_k_3471_);
lean_dec(v_ctorIdx_3468_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object* v_t_3473_, lean_object* v_sticky_3474_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3473_, v_sticky_3474_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object* v_motive_3476_, lean_object* v_t_3477_, lean_object* v_h_3478_, lean_object* v_sticky_3479_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3477_, v_sticky_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object* v_t_3481_, lean_object* v_nonSticky_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3481_, v_nonSticky_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object* v_motive_3484_, lean_object* v_t_3485_, lean_object* v_h_3486_, lean_object* v_nonSticky_3487_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3485_, v_nonSticky_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object* v_x_3489_){
_start:
{
if (lean_obj_tag(v_x_3489_) == 0)
{
uint8_t v___x_3490_; 
v___x_3490_ = 1;
return v___x_3490_;
}
else
{
uint8_t v___x_3491_; 
v___x_3491_ = 0;
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object* v_x_3492_){
_start:
{
uint8_t v_res_3493_; lean_object* v_r_3494_; 
v_res_3493_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_x_3492_);
lean_dec_ref(v_x_3492_);
v_r_3494_ = lean_box(v_res_3493_);
return v_r_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object* v_x_3495_){
_start:
{
lean_object* v_sepArrayFormat_3496_; 
v_sepArrayFormat_3496_ = lean_ctor_get(v_x_3495_, 0);
lean_inc_ref(v_sepArrayFormat_3496_);
return v_sepArrayFormat_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object* v_x_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(v_x_3497_);
lean_dec_ref(v_x_3497_);
return v_res_3498_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3499_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3500_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
lean_ctor_set(v___x_3501_, 1, v___x_3499_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object* v_sep_3502_, lean_object* v_keyword_3503_, lean_object* v_sepArray_3504_, lean_object* v_format_3505_){
_start:
{
lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___x_3544_; lean_object* v___y_3546_; uint8_t v___y_3547_; lean_object* v___y_3552_; uint8_t v___y_3553_; lean_object* v___y_3569_; lean_object* v_sepArrayFormat_3573_; 
v___x_3544_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_sepArrayFormat_3573_ = lean_ctor_get(v_format_3505_, 0);
lean_inc_ref(v_sepArrayFormat_3573_);
v___y_3569_ = v_sepArrayFormat_3573_;
goto v___jp_3568_;
v___jp_3506_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v_nonStickyDoc_3533_; uint8_t v___x_3534_; 
lean_inc_ref(v_keyword_3503_);
v___x_3510_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3503_);
v___x_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v___x_3512_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v___x_3511_);
v___x_3513_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3511_, v___x_3512_);
v___x_3514_ = lean_box(0);
lean_inc_ref(v___y_3507_);
lean_inc_ref(v_sep_3502_);
v___x_3515_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3502_, v___y_3509_, v___y_3507_);
lean_dec_ref(v___y_3509_);
v___x_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
v___x_3517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3514_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
lean_ctor_set(v___x_3517_, 2, v___x_3514_);
v___x_3518_ = lean_unsigned_to_nat(2u);
v___x_3519_ = lean_mk_empty_array_with_capacity(v___x_3518_);
lean_inc_ref_n(v___x_3519_, 3);
v___x_3520_ = lean_array_push(v___x_3519_, v___x_3513_);
v___x_3521_ = lean_array_push(v___x_3520_, v___x_3517_);
v___x_3522_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3521_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_3524_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3511_, v___x_3523_);
v___x_3525_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3502_, v___y_3508_, v___y_3507_);
lean_dec_ref(v___y_3508_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3514_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
lean_ctor_set(v___x_3527_, 2, v___x_3514_);
v___x_3528_ = lean_array_push(v___x_3519_, v___x_3524_);
lean_inc_ref(v___x_3527_);
v___x_3529_ = lean_array_push(v___x_3528_, v___x_3527_);
v___x_3530_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3529_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = lean_array_push(v___x_3519_, v___x_3522_);
v___x_3532_ = lean_array_push(v___x_3531_, v___x_3530_);
v_nonStickyDoc_3533_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3532_);
v___x_3534_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3505_);
lean_dec_ref(v_format_3505_);
if (v___x_3534_ == 0)
{
lean_dec_ref_known(v___x_3527_, 3);
lean_dec_ref(v___x_3519_);
lean_dec_ref(v_keyword_3503_);
return v_nonStickyDoc_3533_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v_stickyDoc_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; 
v___x_3535_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3503_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___x_3537_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3538_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3536_, v___x_3537_);
v___x_3539_ = lean_array_push(v___x_3519_, v___x_3538_);
v___x_3540_ = lean_array_push(v___x_3539_, v___x_3527_);
v_stickyDoc_3541_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3540_);
lean_dec_ref(v___x_3540_);
v___x_3542_ = 0;
v___x_3543_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3533_, v_stickyDoc_3541_, v___x_3542_);
return v___x_3543_;
}
}
v___jp_3545_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = lean_array_get(v___x_3544_, v___y_3546_, v___x_3548_);
lean_dec_ref(v___y_3546_);
v___x_3550_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3503_, v___x_3549_, v___y_3547_);
return v___x_3550_;
}
v___jp_3551_:
{
lean_object* v_sepArray_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
lean_inc_ref(v_sep_3502_);
v_sepArray_3554_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_3502_, v_sepArray_3504_, v___y_3553_);
v___x_3555_ = lean_array_get_size(v_sepArray_3554_);
v___x_3556_ = lean_unsigned_to_nat(1u);
v___x_3557_ = lean_nat_dec_eq(v___x_3555_, v___x_3556_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3558_ = lean_unsigned_to_nat(0u);
v___x_3559_ = lean_nat_dec_lt(v___x_3558_, v___x_3555_);
if (v___x_3559_ == 0)
{
lean_inc_ref(v_sepArray_3554_);
v___y_3507_ = v___y_3552_;
v___y_3508_ = v_sepArray_3554_;
v___y_3509_ = v_sepArray_3554_;
goto v___jp_3506_;
}
else
{
lean_object* v_v_3560_; lean_object* v___x_3561_; lean_object* v_xs_x27_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_v_3560_ = lean_array_fget(v_sepArray_3554_, v___x_3558_);
v___x_3561_ = lean_box(0);
lean_inc_ref(v_sepArray_3554_);
v_xs_x27_3562_ = lean_array_fset(v_sepArray_3554_, v___x_3558_, v___x_3561_);
v___x_3563_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_3560_);
v___x_3564_ = lean_array_fset(v_xs_x27_3562_, v___x_3558_, v___x_3563_);
v___y_3507_ = v___y_3552_;
v___y_3508_ = v_sepArray_3554_;
v___y_3509_ = v___x_3564_;
goto v___jp_3506_;
}
}
else
{
uint8_t v___x_3565_; 
lean_dec_ref(v___y_3552_);
lean_dec_ref(v_sep_3502_);
v___x_3565_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3505_);
lean_dec_ref(v_format_3505_);
if (v___x_3565_ == 0)
{
uint8_t v___x_3566_; 
v___x_3566_ = 1;
v___y_3546_ = v_sepArray_3554_;
v___y_3547_ = v___x_3566_;
goto v___jp_3545_;
}
else
{
uint8_t v___x_3567_; 
v___x_3567_ = 0;
v___y_3546_ = v_sepArray_3554_;
v___y_3547_ = v___x_3567_;
goto v___jp_3545_;
}
}
}
v___jp_3568_:
{
switch(lean_obj_tag(v___y_3569_))
{
case 1:
{
uint8_t v_trailingSep_3570_; 
v_trailingSep_3570_ = lean_ctor_get_uint8(v___y_3569_, sizeof(void*)*1 + 1);
v___y_3552_ = v___y_3569_;
v___y_3553_ = v_trailingSep_3570_;
goto v___jp_3551_;
}
case 3:
{
uint8_t v_trailingSep_3571_; 
v_trailingSep_3571_ = lean_ctor_get_uint8(v___y_3569_, sizeof(void*)*1);
v___y_3552_ = v___y_3569_;
v___y_3553_ = v_trailingSep_3571_;
goto v___jp_3551_;
}
default: 
{
uint8_t v_trailingSep_3572_; 
v_trailingSep_3572_ = lean_ctor_get_uint8(v___y_3569_, sizeof(void*)*2);
v___y_3552_ = v___y_3569_;
v___y_3553_ = v_trailingSep_3572_;
goto v___jp_3551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object* v_sep_3574_, lean_object* v_keyword_3575_, lean_object* v_sepArray_3576_, lean_object* v_format_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3574_, v_keyword_3575_, v_sepArray_3576_, v_format_3577_);
lean_dec_ref(v_sepArray_3576_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(uint8_t v_x_3579_){
_start:
{
if (v_x_3579_ == 0)
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_unsigned_to_nat(0u);
return v___x_3580_;
}
else
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_unsigned_to_nat(1u);
return v___x_3581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___boxed(lean_object* v_x_3582_){
_start:
{
uint8_t v_x_boxed_3583_; lean_object* v_res_3584_; 
v_x_boxed_3583_ = lean_unbox(v_x_3582_);
v_res_3584_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(v_x_boxed_3583_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object* v_k_3585_){
_start:
{
lean_inc(v_k_3585_);
return v_k_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object* v_k_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(v_k_3586_);
lean_dec(v_k_3586_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object* v_motive_3588_, lean_object* v_ctorIdx_3589_, uint8_t v_t_3590_, lean_object* v_h_3591_, lean_object* v_k_3592_){
_start:
{
lean_inc(v_k_3592_);
return v_k_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object* v_motive_3593_, lean_object* v_ctorIdx_3594_, lean_object* v_t_3595_, lean_object* v_h_3596_, lean_object* v_k_3597_){
_start:
{
uint8_t v_t_boxed_3598_; lean_object* v_res_3599_; 
v_t_boxed_3598_ = lean_unbox(v_t_3595_);
v_res_3599_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(v_motive_3593_, v_ctorIdx_3594_, v_t_boxed_3598_, v_h_3596_, v_k_3597_);
lean_dec(v_k_3597_);
lean_dec(v_ctorIdx_3594_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object* v_sticky_3600_){
_start:
{
lean_inc(v_sticky_3600_);
return v_sticky_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3601_){
_start:
{
lean_object* v_res_3602_; 
v_res_3602_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(v_sticky_3601_);
lean_dec(v_sticky_3601_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object* v_motive_3603_, uint8_t v_t_3604_, lean_object* v_h_3605_, lean_object* v_sticky_3606_){
_start:
{
lean_inc(v_sticky_3606_);
return v_sticky_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object* v_motive_3607_, lean_object* v_t_3608_, lean_object* v_h_3609_, lean_object* v_sticky_3610_){
_start:
{
uint8_t v_t_boxed_3611_; lean_object* v_res_3612_; 
v_t_boxed_3611_ = lean_unbox(v_t_3608_);
v_res_3612_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(v_motive_3607_, v_t_boxed_3611_, v_h_3609_, v_sticky_3610_);
lean_dec(v_sticky_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3613_){
_start:
{
lean_inc(v_nonSticky_3613_);
return v_nonSticky_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(v_nonSticky_3614_);
lean_dec(v_nonSticky_3614_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object* v_motive_3616_, uint8_t v_t_3617_, lean_object* v_h_3618_, lean_object* v_nonSticky_3619_){
_start:
{
lean_inc(v_nonSticky_3619_);
return v_nonSticky_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object* v_motive_3620_, lean_object* v_t_3621_, lean_object* v_h_3622_, lean_object* v_nonSticky_3623_){
_start:
{
uint8_t v_t_boxed_3624_; lean_object* v_res_3625_; 
v_t_boxed_3624_ = lean_unbox(v_t_3621_);
v_res_3625_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(v_motive_3620_, v_t_boxed_3624_, v_h_3622_, v_nonSticky_3623_);
lean_dec(v_nonSticky_3623_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object* v_sep_3630_, lean_object* v_keyword_3631_, lean_object* v_sepArray_3632_, uint8_t v_format_3633_){
_start:
{
if (v_format_3633_ == 0)
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0));
v___x_3635_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3630_, v_keyword_3631_, v_sepArray_3632_, v___x_3634_);
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1));
v___x_3637_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3630_, v_keyword_3631_, v_sepArray_3632_, v___x_3636_);
return v___x_3637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object* v_sep_3638_, lean_object* v_keyword_3639_, lean_object* v_sepArray_3640_, lean_object* v_format_3641_){
_start:
{
uint8_t v_format_boxed_3642_; lean_object* v_res_3643_; 
v_format_boxed_3642_ = lean_unbox(v_format_3641_);
v_res_3643_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v_sep_3638_, v_keyword_3639_, v_sepArray_3640_, v_format_boxed_3642_);
lean_dec_ref(v_sepArray_3640_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object* v_format_3644_, lean_object* v_a_3645_){
_start:
{
uint8_t v_nestedRhs_3646_; 
v_nestedRhs_3646_ = lean_ctor_get_uint8(v_format_3644_, 1);
if (v_nestedRhs_3646_ == 0)
{
return v_a_3645_;
}
else
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_Fmt_TaggedDoc_nested(v_a_3645_);
return v___x_3647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object* v_format_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(v_format_3648_, v_a_3649_);
lean_dec_ref(v_format_3648_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object* v_format_3651_){
_start:
{
uint8_t v_allowFlattening_3652_; 
v_allowFlattening_3652_ = lean_ctor_get_uint8(v_format_3651_, 0);
if (v_allowFlattening_3652_ == 0)
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_Fmt_TaggedDoc_hardNl;
return v___x_3653_;
}
else
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_Fmt_TaggedDoc_nl;
return v___x_3654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object* v_format_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3655_);
lean_dec_ref(v_format_3655_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object* v_rhs_3657_, lean_object* v_format_3658_, lean_object* v_lhs_3659_){
_start:
{
uint8_t v_allowFlattening_3660_; 
v_allowFlattening_3660_ = lean_ctor_get_uint8(v_format_3658_, 0);
if (v_allowFlattening_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_lhs_3659_);
v___x_3662_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3658_);
v___x_3663_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3663_, 0, v_format_3658_);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
v___x_3665_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3661_, v___x_3664_);
v___x_3666_ = lean_box(0);
v___x_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3667_, 0, v_rhs_3657_);
v___x_3668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
lean_ctor_set(v___x_3668_, 2, v___x_3666_);
v___x_3669_ = lean_unsigned_to_nat(2u);
v___x_3670_ = lean_mk_empty_array_with_capacity(v___x_3669_);
v___x_3671_ = lean_array_push(v___x_3670_, v___x_3665_);
v___x_3672_ = lean_array_push(v___x_3671_, v___x_3668_);
v___x_3673_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3672_);
lean_dec_ref(v___x_3672_);
return v___x_3673_;
}
else
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3674_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3658_);
v___x_3675_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3675_, 0, v_format_3658_);
v___x_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_3659_, v___x_3676_, v_rhs_3657_, v_allowFlattening_3660_);
return v___x_3677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0(lean_object* v___y_3678_){
_start:
{
lean_inc_ref(v___y_3678_);
return v___y_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed(lean_object* v___y_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Lean_Fmt_Layouts_keywordSeparated___lam__0(v___y_3679_);
lean_dec_ref(v___y_3679_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object* v_lhs_3682_, lean_object* v_keywordTk_3683_, lean_object* v_rhs_3684_, lean_object* v_format_3685_){
_start:
{
uint8_t v___x_3686_; 
v___x_3686_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keywordTk_3683_);
if (v___x_3686_ == 0)
{
lean_object* v___f_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v_trailingKeywordLhs_3693_; lean_object* v___x_3694_; lean_object* v_leadingKeywordRhs_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___f_3687_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3688_ = lean_unsigned_to_nat(2u);
v___x_3689_ = lean_mk_empty_array_with_capacity(v___x_3688_);
lean_inc_ref(v_lhs_3682_);
lean_inc_ref_n(v___x_3689_, 2);
v___x_3690_ = lean_array_push(v___x_3689_, v_lhs_3682_);
lean_inc_ref(v_keywordTk_3683_);
v___x_3691_ = lean_array_push(v___x_3690_, v_keywordTk_3683_);
v___x_3692_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3691_);
lean_dec_ref(v___x_3691_);
v_trailingKeywordLhs_3693_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3692_);
lean_inc_ref_n(v_format_3685_, 2);
lean_inc_ref(v_rhs_3684_);
v___x_3694_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3684_, v_format_3685_, v_keywordTk_3683_);
v_leadingKeywordRhs_3695_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3694_);
v___x_3696_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3684_, v_format_3685_, v_trailingKeywordLhs_3693_);
v___x_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_lhs_3682_);
v___x_3698_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3685_);
lean_dec_ref(v_format_3685_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_ctor_set(v___x_3699_, 1, v___f_3687_);
v___x_3700_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3697_, v___x_3699_);
v___x_3701_ = lean_box(0);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_leadingKeywordRhs_3695_);
v___x_3703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
lean_ctor_set(v___x_3703_, 2, v___x_3701_);
v___x_3704_ = lean_array_push(v___x_3689_, v___x_3700_);
v___x_3705_ = lean_array_push(v___x_3704_, v___x_3703_);
v___x_3706_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3705_);
lean_dec_ref(v___x_3705_);
v___x_3707_ = lean_array_push(v___x_3689_, v___x_3696_);
v___x_3708_ = lean_array_push(v___x_3707_, v___x_3706_);
v___x_3709_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3708_);
v___x_3710_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3709_);
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec_ref(v_keywordTk_3683_);
v___x_3711_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3684_, v_format_3685_, v_lhs_3682_);
v___x_3712_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3711_);
return v___x_3712_;
}
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0(void){
_start:
{
lean_object* v___f_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___f_3713_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3714_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v___f_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object* v_terms_3716_){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3717_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3718_ = lean_box(0);
v___x_3719_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_terms_3716_);
v___x_3720_ = lean_array_pop(v_terms_3716_);
v___x_3721_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_3719_, v___x_3720_);
v___x_3722_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3721_);
v___x_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3718_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
lean_ctor_set(v___x_3724_, 2, v___x_3718_);
v___x_3725_ = lean_array_get_size(v_terms_3716_);
v___x_3726_ = lean_unsigned_to_nat(1u);
v___x_3727_ = lean_nat_sub(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_array_get(v___x_3717_, v_terms_3716_, v___x_3727_);
lean_dec(v___x_3727_);
lean_dec_ref(v_terms_3716_);
v___x_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
v___x_3730_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_3731_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_3729_, v___x_3730_);
v___x_3732_ = lean_unsigned_to_nat(2u);
v___x_3733_ = lean_mk_empty_array_with_capacity(v___x_3732_);
v___x_3734_ = lean_array_push(v___x_3733_, v___x_3724_);
v___x_3735_ = lean_array_push(v___x_3734_, v___x_3731_);
v___x_3736_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3735_);
lean_dec_ref(v___x_3735_);
return v___x_3736_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0(void){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3738_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object* v_app_3739_, lean_object* v_fillableTerms_3740_, lean_object* v_terms_3741_, lean_object* v_eligibleKinds_3742_){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; uint8_t v_allowFill_3749_; 
v___x_3743_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3744_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3745_ = lean_array_get_size(v_fillableTerms_3740_);
v___x_3746_ = lean_unsigned_to_nat(1u);
v___x_3747_ = lean_nat_sub(v___x_3745_, v___x_3746_);
v___x_3748_ = lean_array_get_borrowed(v___x_3744_, v_fillableTerms_3740_, v___x_3747_);
lean_dec(v___x_3747_);
v_allowFill_3749_ = lean_ctor_get_uint8(v___x_3748_, sizeof(void*)*1);
if (v_allowFill_3749_ == 0)
{
lean_object* v___x_3750_; 
lean_dec_ref(v_terms_3741_);
lean_dec_ref(v_app_3739_);
v___x_3750_ = lean_box(0);
return v___x_3750_;
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3751_ = lean_array_get_size(v_terms_3741_);
v___x_3752_ = lean_nat_sub(v___x_3751_, v___x_3746_);
v___x_3753_ = lean_array_get_borrowed(v___x_3743_, v_terms_3741_, v___x_3752_);
lean_inc(v___x_3753_);
v___x_3754_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v___x_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v___x_3755_; 
lean_dec(v___x_3752_);
lean_dec_ref(v_terms_3741_);
lean_dec_ref(v_app_3739_);
v___x_3755_ = lean_box(0);
return v___x_3755_;
}
else
{
lean_object* v_val_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3777_; 
v_val_3756_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3758_ = v___x_3754_;
v_isShared_3759_ = v_isSharedCheck_3777_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_val_3756_);
lean_dec(v___x_3754_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3777_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
uint8_t v___x_3760_; uint8_t v___x_3761_; lean_object* v___y_3763_; 
v___x_3760_ = lean_unbox(v_val_3756_);
lean_dec(v_val_3756_);
v___x_3761_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_3742_, v___x_3760_);
if (v___x_3761_ == 0)
{
lean_object* v___x_3772_; 
lean_del_object(v___x_3758_);
lean_dec(v___x_3752_);
lean_dec_ref(v_terms_3741_);
lean_dec_ref(v_app_3739_);
v___x_3772_ = lean_box(0);
return v___x_3772_;
}
else
{
lean_object* v___x_3773_; 
lean_inc(v___x_3753_);
v___x_3773_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_3753_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_3775_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_3774_);
v___y_3763_ = v___x_3775_;
goto v___jp_3762_;
}
else
{
lean_object* v_val_3776_; 
v_val_3776_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v___x_3773_, 1);
v___y_3763_ = v_val_3776_;
goto v___jp_3762_;
}
}
v___jp_3762_:
{
lean_object* v_stickyVariant_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v_stickyVariant_3764_ = lean_ctor_get(v___y_3763_, 0);
lean_inc_ref(v_stickyVariant_3764_);
v___x_3765_ = lean_array_set(v_terms_3741_, v___x_3752_, v_stickyVariant_3764_);
lean_dec(v___x_3752_);
v___x_3766_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v___x_3765_);
v___x_3767_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_3763_, v___x_3761_);
lean_dec_ref(v___y_3763_);
v___x_3768_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_app_3739_, v___x_3766_, v___x_3767_);
lean_dec(v___x_3767_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 0, v___x_3768_);
v___x_3770_ = v___x_3758_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object* v_app_3778_, lean_object* v_fillableTerms_3779_, lean_object* v_terms_3780_, lean_object* v_eligibleKinds_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3778_, v_fillableTerms_3779_, v_terms_3780_, v_eligibleKinds_3781_);
lean_dec_ref(v_eligibleKinds_3781_);
lean_dec_ref(v_fillableTerms_3779_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object* v_format_3783_, lean_object* v_app_3784_, lean_object* v_terms_3785_){
_start:
{
uint8_t v_sparse_3786_; 
v_sparse_3786_ = lean_ctor_get_uint8(v_format_3783_, 1);
if (v_sparse_3786_ == 0)
{
uint8_t v_respectPseudoAlignment_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v_respectPseudoAlignment_3787_ = lean_ctor_get_uint8(v_format_3783_, 3);
v___x_3788_ = lean_array_get_size(v_terms_3785_);
v___x_3789_ = lean_unsigned_to_nat(2u);
v___x_3790_ = lean_nat_dec_eq(v___x_3788_, v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec_ref(v_terms_3785_);
lean_dec_ref(v_app_3784_);
v___x_3791_ = lean_box(0);
return v___x_3791_;
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v___x_3792_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3793_ = lean_unsigned_to_nat(1u);
v___x_3794_ = lean_nat_sub(v___x_3788_, v___x_3793_);
v___x_3795_ = lean_array_get_borrowed(v___x_3792_, v_terms_3785_, v___x_3794_);
lean_dec(v___x_3794_);
lean_inc(v___x_3795_);
v___x_3796_ = l_Lean_Fmt_Layouts_permitDenseLayout(v___x_3795_, v_respectPseudoAlignment_3787_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; 
lean_dec_ref(v_terms_3785_);
lean_dec_ref(v_app_3784_);
v___x_3797_ = lean_box(0);
return v___x_3797_;
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3798_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v_terms_3785_);
v___x_3799_ = lean_mk_empty_array_with_capacity(v___x_3789_);
v___x_3800_ = lean_array_push(v___x_3799_, v___x_3798_);
v___x_3801_ = lean_array_push(v___x_3800_, v_app_3784_);
v___x_3802_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3801_);
v___x_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
}
}
else
{
lean_object* v___x_3804_; 
lean_dec_ref(v_terms_3785_);
lean_dec_ref(v_app_3784_);
v___x_3804_ = lean_box(0);
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object* v_format_3805_, lean_object* v_app_3806_, lean_object* v_terms_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3805_, v_app_3806_, v_terms_3807_);
lean_dec_ref(v_format_3805_);
return v_res_3808_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0));
v___x_3811_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3810_);
return v___x_3811_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3812_; lean_object* v_lbTk_3813_; 
v___x_3812_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1);
v_lbTk_3813_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3812_);
return v_lbTk_3813_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3));
v___x_3816_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3815_);
return v___x_3816_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3817_; lean_object* v_rbTk_3818_; 
v___x_3817_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4);
v_rbTk_3818_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3817_);
return v_rbTk_3818_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object* v_upperBound_3819_, lean_object* v_a_3820_, lean_object* v_b_3821_){
_start:
{
lean_object* v_a_3823_; uint8_t v___x_3827_; 
v___x_3827_ = lean_nat_dec_lt(v_a_3820_, v_upperBound_3819_);
if (v___x_3827_ == 0)
{
lean_dec(v_a_3820_);
return v_b_3821_;
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v_v_3830_; uint8_t v_allowFill_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3843_; 
v___x_3828_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3829_ = lean_array_get(v___x_3828_, v_b_3821_, v_a_3820_);
v_v_3830_ = lean_ctor_get(v___x_3829_, 0);
v_allowFill_3831_ = lean_ctor_get_uint8(v___x_3829_, sizeof(void*)*1);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3833_ = v___x_3829_;
v_isShared_3834_ = v_isSharedCheck_3843_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_v_3830_);
lean_dec(v___x_3829_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3843_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
uint8_t v___x_3835_; 
lean_inc(v_v_3830_);
v___x_3835_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_v_3830_);
if (v___x_3835_ == 0)
{
lean_del_object(v___x_3833_);
lean_dec(v_v_3830_);
v_a_3823_ = v_b_3821_;
goto v___jp_3822_;
}
else
{
lean_object* v_lbTk_3836_; lean_object* v_rbTk_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
v_lbTk_3836_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2);
v_rbTk_3837_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5);
v___x_3838_ = l_Lean_Fmt_Layouts_parens(v_lbTk_3836_, v_v_3830_, v_rbTk_3837_);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3838_);
v___x_3840_ = v___x_3833_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3838_);
lean_ctor_set_uint8(v_reuseFailAlloc_3842_, sizeof(void*)*1, v_allowFill_3831_);
v___x_3840_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_array_set(v_b_3821_, v_a_3820_, v___x_3840_);
v_a_3823_ = v___x_3841_;
goto v___jp_3822_;
}
}
}
}
v___jp_3822_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = lean_unsigned_to_nat(1u);
v___x_3825_ = lean_nat_add(v_a_3820_, v___x_3824_);
lean_dec(v_a_3820_);
v_a_3820_ = v___x_3825_;
v_b_3821_ = v_a_3823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object* v_upperBound_3844_, lean_object* v_a_3845_, lean_object* v_b_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3844_, v_a_3845_, v_b_3846_);
lean_dec(v_upperBound_3844_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object* v_as_3848_, size_t v_i_3849_, size_t v_stop_3850_, lean_object* v_b_3851_){
_start:
{
lean_object* v___y_3853_; uint8_t v___x_3857_; 
v___x_3857_ = lean_usize_dec_eq(v_i_3849_, v_stop_3850_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; lean_object* v_v_3859_; uint8_t v___x_3860_; 
v___x_3858_ = lean_array_uget_borrowed(v_as_3848_, v_i_3849_);
v_v_3859_ = lean_ctor_get(v___x_3858_, 0);
v___x_3860_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_inc(v___x_3858_);
v___x_3861_ = lean_array_push(v_b_3851_, v___x_3858_);
v___y_3853_ = v___x_3861_;
goto v___jp_3852_;
}
else
{
v___y_3853_ = v_b_3851_;
goto v___jp_3852_;
}
}
else
{
return v_b_3851_;
}
v___jp_3852_:
{
size_t v___x_3854_; size_t v___x_3855_; 
v___x_3854_ = ((size_t)1ULL);
v___x_3855_ = lean_usize_add(v_i_3849_, v___x_3854_);
v_i_3849_ = v___x_3855_;
v_b_3851_ = v___y_3853_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object* v_as_3862_, lean_object* v_i_3863_, lean_object* v_stop_3864_, lean_object* v_b_3865_){
_start:
{
size_t v_i_boxed_3866_; size_t v_stop_boxed_3867_; lean_object* v_res_3868_; 
v_i_boxed_3866_ = lean_unbox_usize(v_i_3863_);
lean_dec(v_i_3863_);
v_stop_boxed_3867_ = lean_unbox_usize(v_stop_3864_);
lean_dec(v_stop_3864_);
v_res_3868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_as_3862_, v_i_boxed_3866_, v_stop_boxed_3867_, v_b_3865_);
lean_dec_ref(v_as_3862_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t v_sz_3869_, size_t v_i_3870_, lean_object* v_bs_3871_){
_start:
{
uint8_t v___x_3872_; 
v___x_3872_ = lean_usize_dec_lt(v_i_3870_, v_sz_3869_);
if (v___x_3872_ == 0)
{
return v_bs_3871_;
}
else
{
lean_object* v_v_3873_; lean_object* v_v_3874_; lean_object* v___x_3875_; lean_object* v_bs_x27_3876_; size_t v___x_3877_; size_t v___x_3878_; lean_object* v___x_3879_; 
v_v_3873_ = lean_array_uget_borrowed(v_bs_3871_, v_i_3870_);
v_v_3874_ = lean_ctor_get(v_v_3873_, 0);
lean_inc(v_v_3874_);
v___x_3875_ = lean_unsigned_to_nat(0u);
v_bs_x27_3876_ = lean_array_uset(v_bs_3871_, v_i_3870_, v___x_3875_);
v___x_3877_ = ((size_t)1ULL);
v___x_3878_ = lean_usize_add(v_i_3870_, v___x_3877_);
v___x_3879_ = lean_array_uset(v_bs_x27_3876_, v_i_3870_, v_v_3874_);
v_i_3870_ = v___x_3878_;
v_bs_3871_ = v___x_3879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object* v_sz_3881_, lean_object* v_i_3882_, lean_object* v_bs_3883_){
_start:
{
size_t v_sz_boxed_3884_; size_t v_i_boxed_3885_; lean_object* v_res_3886_; 
v_sz_boxed_3884_ = lean_unbox_usize(v_sz_3881_);
lean_dec(v_sz_3881_);
v_i_boxed_3885_ = lean_unbox_usize(v_i_3882_);
lean_dec(v_i_3882_);
v_res_3886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_boxed_3884_, v_i_boxed_3885_, v_bs_3883_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object* v_terms_3889_, lean_object* v_format_3890_){
_start:
{
lean_object* v_app_3892_; lean_object* v_fillableTerms_3896_; lean_object* v___y_3910_; lean_object* v_fillableTerms_3911_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___y_3919_; lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3916_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3944_ = lean_array_get_size(v_terms_3889_);
v___x_3945_ = ((lean_object*)(l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0));
v___x_3946_ = lean_nat_dec_lt(v___x_3917_, v___x_3944_);
if (v___x_3946_ == 0)
{
v___y_3919_ = v___x_3945_;
goto v___jp_3918_;
}
else
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_nat_dec_le(v___x_3944_, v___x_3944_);
if (v___x_3947_ == 0)
{
if (v___x_3946_ == 0)
{
v___y_3919_ = v___x_3945_;
goto v___jp_3918_;
}
else
{
size_t v___x_3948_; size_t v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = ((size_t)0ULL);
v___x_3949_ = lean_usize_of_nat(v___x_3944_);
v___x_3950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3889_, v___x_3948_, v___x_3949_, v___x_3945_);
v___y_3919_ = v___x_3950_;
goto v___jp_3918_;
}
}
else
{
size_t v___x_3951_; size_t v___x_3952_; lean_object* v___x_3953_; 
v___x_3951_ = ((size_t)0ULL);
v___x_3952_ = lean_usize_of_nat(v___x_3944_);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3889_, v___x_3951_, v___x_3952_, v___x_3945_);
v___y_3919_ = v___x_3953_;
goto v___jp_3918_;
}
}
v___jp_3891_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = l_Lean_Fmt_TaggedDoc_nested(v_app_3892_);
v___x_3894_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3893_);
return v___x_3894_;
}
v___jp_3895_:
{
lean_object* v_app_3897_; size_t v_sz_3898_; size_t v___x_3899_; lean_object* v_terms_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
lean_inc_ref_n(v_fillableTerms_3896_, 2);
v_app_3897_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(v_fillableTerms_3896_);
v_sz_3898_ = lean_array_size(v_fillableTerms_3896_);
v___x_3899_ = ((size_t)0ULL);
v_terms_3900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_3898_, v___x_3899_, v_fillableTerms_3896_);
v___x_3901_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
lean_inc_ref(v_terms_3900_);
lean_inc_ref(v_app_3897_);
v___x_3902_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3897_, v_fillableTerms_3896_, v_terms_3900_, v___x_3901_);
if (lean_obj_tag(v___x_3902_) == 1)
{
lean_object* v_val_3903_; 
lean_dec_ref(v_terms_3900_);
lean_dec_ref(v_app_3897_);
lean_dec_ref(v_fillableTerms_3896_);
v_val_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_val_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v_app_3892_ = v_val_3903_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3904_; 
lean_dec(v___x_3902_);
lean_inc_ref(v_terms_3900_);
lean_inc_ref(v_app_3897_);
v___x_3904_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3890_, v_app_3897_, v_terms_3900_);
if (lean_obj_tag(v___x_3904_) == 1)
{
lean_object* v_val_3905_; 
lean_dec_ref(v_terms_3900_);
lean_dec_ref(v_app_3897_);
lean_dec_ref(v_fillableTerms_3896_);
v_val_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_val_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v_app_3892_ = v_val_3905_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
lean_dec(v___x_3904_);
v___x_3906_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
lean_inc_ref(v_app_3897_);
v___x_3907_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3897_, v_fillableTerms_3896_, v_terms_3900_, v___x_3906_);
lean_dec_ref(v_fillableTerms_3896_);
if (lean_obj_tag(v___x_3907_) == 1)
{
lean_object* v_val_3908_; 
lean_dec_ref(v_app_3897_);
v_val_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_val_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v_app_3892_ = v_val_3908_;
goto v___jp_3891_;
}
else
{
lean_dec(v___x_3907_);
v_app_3892_ = v_app_3897_;
goto v___jp_3891_;
}
}
}
}
v___jp_3909_:
{
uint8_t v_parenthesize_3912_; 
v_parenthesize_3912_ = lean_ctor_get_uint8(v_format_3890_, 2);
if (v_parenthesize_3912_ == 0)
{
lean_dec(v___y_3910_);
v_fillableTerms_3896_ = v_fillableTerms_3911_;
goto v___jp_3895_;
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3913_ = lean_array_get_size(v_fillableTerms_3911_);
v___x_3914_ = lean_nat_sub(v___x_3913_, v___y_3910_);
v___x_3915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v___x_3914_, v___y_3910_, v_fillableTerms_3911_);
lean_dec(v___x_3914_);
v_fillableTerms_3896_ = v___x_3915_;
goto v___jp_3895_;
}
}
v___jp_3918_:
{
lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3920_ = lean_array_get_size(v___y_3919_);
v___x_3921_ = lean_nat_dec_eq(v___x_3920_, v___x_3917_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; uint8_t v___x_3923_; 
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = lean_nat_dec_eq(v___x_3920_, v___x_3922_);
if (v___x_3923_ == 0)
{
uint8_t v___x_3924_; 
v___x_3924_ = lean_nat_dec_lt(v___x_3922_, v___x_3920_);
if (v___x_3924_ == 0)
{
v___y_3910_ = v___x_3922_;
v_fillableTerms_3911_ = v___y_3919_;
goto v___jp_3909_;
}
else
{
uint8_t v_hardNestedFirstTerm_3925_; 
v_hardNestedFirstTerm_3925_ = lean_ctor_get_uint8(v_format_3890_, 0);
if (v_hardNestedFirstTerm_3925_ == 0)
{
v___y_3910_ = v___x_3922_;
v_fillableTerms_3911_ = v___y_3919_;
goto v___jp_3909_;
}
else
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_nat_dec_lt(v___x_3917_, v___x_3920_);
if (v___x_3926_ == 0)
{
v___y_3910_ = v___x_3922_;
v_fillableTerms_3911_ = v___y_3919_;
goto v___jp_3909_;
}
else
{
lean_object* v_v_3927_; lean_object* v_v_3928_; uint8_t v_allowFill_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3940_; 
v_v_3927_ = lean_array_fget(v___y_3919_, v___x_3917_);
v_v_3928_ = lean_ctor_get(v_v_3927_, 0);
v_allowFill_3929_ = lean_ctor_get_uint8(v_v_3927_, sizeof(void*)*1);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_v_3927_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3931_ = v_v_3927_;
v_isShared_3932_ = v_isSharedCheck_3940_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_v_3928_);
lean_dec(v_v_3927_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3940_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3933_; lean_object* v_xs_x27_3934_; lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3933_ = lean_box(0);
v_xs_x27_3934_ = lean_array_fset(v___y_3919_, v___x_3917_, v___x_3933_);
v___x_3935_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3928_);
if (v_isShared_3932_ == 0)
{
lean_ctor_set(v___x_3931_, 0, v___x_3935_);
v___x_3937_ = v___x_3931_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3935_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*1, v_allowFill_3929_);
v___x_3937_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_array_fset(v_xs_x27_3934_, v___x_3917_, v___x_3937_);
v___y_3910_ = v___x_3922_;
v_fillableTerms_3911_ = v___x_3938_;
goto v___jp_3909_;
}
}
}
}
}
}
else
{
lean_object* v___x_3941_; lean_object* v_v_3942_; 
v___x_3941_ = lean_array_get(v___x_3916_, v___y_3919_, v___x_3917_);
lean_dec_ref(v___y_3919_);
v_v_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_v_3942_);
lean_dec(v___x_3941_);
return v_v_3942_;
}
}
else
{
lean_object* v___x_3943_; 
lean_dec_ref(v___y_3919_);
v___x_3943_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object* v_terms_3954_, lean_object* v_format_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v_terms_3954_, v_format_3955_);
lean_dec_ref(v_format_3955_);
lean_dec_ref(v_terms_3954_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object* v_upperBound_3957_, lean_object* v_inst_3958_, lean_object* v_R_3959_, lean_object* v_a_3960_, lean_object* v_b_3961_, lean_object* v_c_3962_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3957_, v_a_3960_, v_b_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object* v_upperBound_3964_, lean_object* v_inst_3965_, lean_object* v_R_3966_, lean_object* v_a_3967_, lean_object* v_b_3968_, lean_object* v_c_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(v_upperBound_3964_, v_inst_3965_, v_R_3966_, v_a_3967_, v_b_3968_, v_c_3969_);
lean_dec(v_upperBound_3964_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t v_sz_3971_, size_t v_i_3972_, lean_object* v_bs_3973_){
_start:
{
uint8_t v___x_3974_; 
v___x_3974_ = lean_usize_dec_lt(v_i_3972_, v_sz_3971_);
if (v___x_3974_ == 0)
{
return v_bs_3973_;
}
else
{
lean_object* v_v_3975_; lean_object* v___x_3976_; lean_object* v_bs_x27_3977_; lean_object* v___x_3978_; size_t v___x_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
v_v_3975_ = lean_array_uget(v_bs_3973_, v_i_3972_);
v___x_3976_ = lean_unsigned_to_nat(0u);
v_bs_x27_3977_ = lean_array_uset(v_bs_3973_, v_i_3972_, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3978_, 0, v_v_3975_);
lean_ctor_set_uint8(v___x_3978_, sizeof(void*)*1, v___x_3974_);
v___x_3979_ = ((size_t)1ULL);
v___x_3980_ = lean_usize_add(v_i_3972_, v___x_3979_);
v___x_3981_ = lean_array_uset(v_bs_x27_3977_, v_i_3972_, v___x_3978_);
v_i_3972_ = v___x_3980_;
v_bs_3973_ = v___x_3981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object* v_sz_3983_, lean_object* v_i_3984_, lean_object* v_bs_3985_){
_start:
{
size_t v_sz_boxed_3986_; size_t v_i_boxed_3987_; lean_object* v_res_3988_; 
v_sz_boxed_3986_ = lean_unbox_usize(v_sz_3983_);
lean_dec(v_sz_3983_);
v_i_boxed_3987_ = lean_unbox_usize(v_i_3984_);
lean_dec(v_i_3984_);
v_res_3988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_boxed_3986_, v_i_boxed_3987_, v_bs_3985_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object* v_terms_3989_, lean_object* v_format_3990_){
_start:
{
size_t v_sz_3991_; size_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v_sz_3991_ = lean_array_size(v_terms_3989_);
v___x_3992_ = ((size_t)0ULL);
v___x_3993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_3991_, v___x_3992_, v_terms_3989_);
v___x_3994_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_3993_, v_format_3990_);
lean_dec_ref(v___x_3993_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object* v_terms_3995_, lean_object* v_format_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_Fmt_Layouts_application(v_terms_3995_, v_format_3996_);
lean_dec_ref(v_format_3996_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object* v_f_3998_){
_start:
{
uint8_t v_hardNestedFirstTerm_3999_; uint8_t v_sparse_4000_; uint8_t v_parenthesize_4001_; uint8_t v_respectPseudoAlignment_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
v_hardNestedFirstTerm_3999_ = lean_ctor_get_uint8(v_f_3998_, 0);
v_sparse_4000_ = lean_ctor_get_uint8(v_f_3998_, 1);
v_parenthesize_4001_ = lean_ctor_get_uint8(v_f_3998_, 2);
v_respectPseudoAlignment_4002_ = lean_ctor_get_uint8(v_f_3998_, 3);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_f_3998_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v_f_3998_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_dec(v_f_3998_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_4008_, 0, v_hardNestedFirstTerm_3999_);
lean_ctor_set_uint8(v_reuseFailAlloc_4008_, 1, v_sparse_4000_);
lean_ctor_set_uint8(v_reuseFailAlloc_4008_, 2, v_parenthesize_4001_);
lean_ctor_set_uint8(v_reuseFailAlloc_4008_, 3, v_respectPseudoAlignment_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object* v_terms_4010_, lean_object* v_format_4011_){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4012_ = l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(v_format_4011_);
v___x_4013_ = l_Lean_Fmt_Layouts_application(v_terms_4010_, v___x_4012_);
lean_dec_ref(v___x_4012_);
return v___x_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(lean_object* v_x_4014_){
_start:
{
if (lean_obj_tag(v_x_4014_) == 0)
{
lean_object* v___x_4015_; 
v___x_4015_ = lean_unsigned_to_nat(0u);
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; 
v___x_4016_ = lean_unsigned_to_nat(1u);
return v___x_4016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___boxed(lean_object* v_x_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(v_x_4017_);
lean_dec_ref(v_x_4017_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object* v_t_4019_, lean_object* v_k_4020_){
_start:
{
lean_object* v_doc_4021_; lean_object* v___x_4022_; 
v_doc_4021_ = lean_ctor_get(v_t_4019_, 0);
lean_inc_ref(v_doc_4021_);
lean_dec_ref(v_t_4019_);
v___x_4022_ = lean_apply_1(v_k_4020_, v_doc_4021_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object* v_motive_4023_, lean_object* v_ctorIdx_4024_, lean_object* v_t_4025_, lean_object* v_h_4026_, lean_object* v_k_4027_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4025_, v_k_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object* v_motive_4029_, lean_object* v_ctorIdx_4030_, lean_object* v_t_4031_, lean_object* v_h_4032_, lean_object* v_k_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(v_motive_4029_, v_ctorIdx_4030_, v_t_4031_, v_h_4032_, v_k_4033_);
lean_dec(v_ctorIdx_4030_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object* v_t_4035_, lean_object* v_sep_4036_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4035_, v_sep_4036_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object* v_motive_4038_, lean_object* v_t_4039_, lean_object* v_h_4040_, lean_object* v_sep_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4039_, v_sep_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object* v_t_4043_, lean_object* v_elems_4044_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4043_, v_elems_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object* v_motive_4046_, lean_object* v_t_4047_, lean_object* v_h_4048_, lean_object* v_elems_4049_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4047_, v_elems_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t v_sz_4051_, size_t v_i_4052_, lean_object* v_bs_4053_){
_start:
{
uint8_t v___x_4054_; 
v___x_4054_ = lean_usize_dec_lt(v_i_4052_, v_sz_4051_);
if (v___x_4054_ == 0)
{
return v_bs_4053_;
}
else
{
lean_object* v_v_4055_; lean_object* v___x_4056_; lean_object* v_bs_x27_4057_; lean_object* v___y_4059_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; 
v_v_4055_ = lean_array_uget(v_bs_4053_, v_i_4052_);
v___x_4056_ = lean_unsigned_to_nat(0u);
v_bs_x27_4057_ = lean_array_uset(v_bs_4053_, v_i_4052_, v___x_4056_);
v___x_4064_ = lean_usize_to_nat(v_i_4052_);
v___x_4065_ = lean_unsigned_to_nat(2u);
v___x_4066_ = lean_nat_mod(v___x_4064_, v___x_4065_);
lean_dec(v___x_4064_);
v___x_4067_ = lean_nat_dec_eq(v___x_4066_, v___x_4056_);
lean_dec(v___x_4066_);
if (v___x_4067_ == 0)
{
lean_object* v___x_4068_; 
v___x_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4068_, 0, v_v_4055_);
v___y_4059_ = v___x_4068_;
goto v___jp_4058_;
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4069_ = lean_unsigned_to_nat(1u);
v___x_4070_ = lean_mk_empty_array_with_capacity(v___x_4069_);
v___x_4071_ = lean_array_push(v___x_4070_, v_v_4055_);
v___x_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
v___y_4059_ = v___x_4072_;
goto v___jp_4058_;
}
v___jp_4058_:
{
size_t v___x_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = ((size_t)1ULL);
v___x_4061_ = lean_usize_add(v_i_4052_, v___x_4060_);
v___x_4062_ = lean_array_uset(v_bs_x27_4057_, v_i_4052_, v___y_4059_);
v_i_4052_ = v___x_4061_;
v_bs_4053_ = v___x_4062_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object* v_sz_4073_, lean_object* v_i_4074_, lean_object* v_bs_4075_){
_start:
{
size_t v_sz_boxed_4076_; size_t v_i_boxed_4077_; lean_object* v_res_4078_; 
v_sz_boxed_4076_ = lean_unbox_usize(v_sz_4073_);
lean_dec(v_sz_4073_);
v_i_boxed_4077_ = lean_unbox_usize(v_i_4074_);
lean_dec(v_i_4074_);
v_res_4078_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_boxed_4076_, v_i_boxed_4077_, v_bs_4075_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object* v_elems_4079_){
_start:
{
size_t v_sz_4080_; size_t v___x_4081_; lean_object* v___x_4082_; 
v_sz_4080_ = lean_array_size(v_elems_4079_);
v___x_4081_ = ((size_t)0ULL);
v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_4080_, v___x_4081_, v_elems_4079_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object* v_s_4083_, lean_object* v_elems_4084_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_elems_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object* v_s_4086_, lean_object* v_elems_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(v_s_4086_, v_elems_4087_);
lean_dec_ref(v_s_4086_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object* v_as_4089_, size_t v_sz_4090_, size_t v_i_4091_, lean_object* v_bs_4092_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_4090_, v_i_4091_, v_bs_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object* v_as_4094_, lean_object* v_sz_4095_, lean_object* v_i_4096_, lean_object* v_bs_4097_){
_start:
{
size_t v_sz_boxed_4098_; size_t v_i_boxed_4099_; lean_object* v_res_4100_; 
v_sz_boxed_4098_ = lean_unbox_usize(v_sz_4095_);
lean_dec(v_sz_4095_);
v_i_boxed_4099_ = lean_unbox_usize(v_i_4096_);
lean_dec(v_i_4096_);
v_res_4100_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(v_as_4094_, v_sz_boxed_4098_, v_i_boxed_4099_, v_bs_4097_);
lean_dec_ref(v_as_4094_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t v_sz_4103_, size_t v_i_4104_, lean_object* v_bs_4105_){
_start:
{
uint8_t v___x_4106_; 
v___x_4106_ = lean_usize_dec_lt(v_i_4104_, v_sz_4103_);
if (v___x_4106_ == 0)
{
return v_bs_4105_;
}
else
{
lean_object* v_v_4107_; lean_object* v___x_4108_; lean_object* v_bs_x27_4109_; lean_object* v___y_4111_; 
v_v_4107_ = lean_array_uget(v_bs_4105_, v_i_4104_);
v___x_4108_ = lean_unsigned_to_nat(0u);
v_bs_x27_4109_ = lean_array_uset(v_bs_4105_, v_i_4104_, v___x_4108_);
if (lean_obj_tag(v_v_4107_) == 0)
{
v___y_4111_ = v_v_4107_;
goto v___jp_4110_;
}
else
{
lean_object* v_docs_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4138_; 
v_docs_4116_ = lean_ctor_get(v_v_4107_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v_v_4107_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4118_ = v_v_4107_;
v_isShared_4119_ = v_isSharedCheck_4138_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_docs_4116_);
lean_dec(v_v_4107_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4138_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4120_ = lean_array_get_size(v_docs_4116_);
v___x_4121_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4122_ = lean_nat_dec_lt(v___x_4108_, v___x_4120_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; 
lean_del_object(v___x_4118_);
lean_dec_ref(v_docs_4116_);
v___x_4123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_4111_ = v___x_4123_;
goto v___jp_4110_;
}
else
{
uint8_t v___x_4124_; 
v___x_4124_ = lean_nat_dec_le(v___x_4120_, v___x_4120_);
if (v___x_4124_ == 0)
{
if (v___x_4122_ == 0)
{
lean_object* v___x_4125_; 
lean_del_object(v___x_4118_);
lean_dec_ref(v_docs_4116_);
v___x_4125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_4111_ = v___x_4125_;
goto v___jp_4110_;
}
else
{
size_t v___x_4126_; size_t v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4126_ = ((size_t)0ULL);
v___x_4127_ = lean_usize_of_nat(v___x_4120_);
v___x_4128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_docs_4116_, v___x_4126_, v___x_4127_, v___x_4121_);
lean_dec_ref(v_docs_4116_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4128_);
v___x_4130_ = v___x_4118_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
v___y_4111_ = v___x_4130_;
goto v___jp_4110_;
}
}
}
else
{
size_t v___x_4132_; size_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4132_ = ((size_t)0ULL);
v___x_4133_ = lean_usize_of_nat(v___x_4120_);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_docs_4116_, v___x_4132_, v___x_4133_, v___x_4121_);
lean_dec_ref(v_docs_4116_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4134_);
v___x_4136_ = v___x_4118_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
v___y_4111_ = v___x_4136_;
goto v___jp_4110_;
}
}
}
}
}
v___jp_4110_:
{
size_t v___x_4112_; size_t v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((size_t)1ULL);
v___x_4113_ = lean_usize_add(v_i_4104_, v___x_4112_);
v___x_4114_ = lean_array_uset(v_bs_x27_4109_, v_i_4104_, v___y_4111_);
v_i_4104_ = v___x_4113_;
v_bs_4105_ = v___x_4114_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object* v_sz_4139_, lean_object* v_i_4140_, lean_object* v_bs_4141_){
_start:
{
size_t v_sz_boxed_4142_; size_t v_i_boxed_4143_; lean_object* v_res_4144_; 
v_sz_boxed_4142_ = lean_unbox_usize(v_sz_4139_);
lean_dec(v_sz_4139_);
v_i_boxed_4143_ = lean_unbox_usize(v_i_4140_);
lean_dec(v_i_4140_);
v_res_4144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_boxed_4142_, v_i_boxed_4143_, v_bs_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object* v_as_4145_, lean_object* v_j_4146_){
_start:
{
lean_object* v___x_4151_; uint8_t v___x_4152_; 
v___x_4151_ = lean_array_get_size(v_as_4145_);
v___x_4152_ = lean_nat_dec_lt(v_j_4146_, v___x_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; 
lean_dec(v_j_4146_);
v___x_4153_ = lean_box(0);
return v___x_4153_;
}
else
{
lean_object* v___x_4154_; 
v___x_4154_ = lean_array_fget(v_as_4145_, v_j_4146_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_dec_ref_known(v___x_4154_, 1);
goto v___jp_4147_;
}
else
{
lean_object* v_docs_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4165_; 
v_docs_4155_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4157_ = v___x_4154_;
v_isShared_4158_ = v_isSharedCheck_4165_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_docs_4155_);
lean_dec(v___x_4154_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4165_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v___x_4159_ = lean_array_get_size(v_docs_4155_);
lean_dec_ref(v_docs_4155_);
v___x_4160_ = lean_unsigned_to_nat(0u);
v___x_4161_ = lean_nat_dec_eq(v___x_4159_, v___x_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4163_; 
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v_j_4146_);
v___x_4163_ = v___x_4157_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_j_4146_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
else
{
lean_del_object(v___x_4157_);
goto v___jp_4147_;
}
}
}
}
v___jp_4147_:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_unsigned_to_nat(1u);
v___x_4149_ = lean_nat_add(v_j_4146_, v___x_4148_);
lean_dec(v_j_4146_);
v_j_4146_ = v___x_4149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object* v_as_4166_, lean_object* v_j_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_as_4166_, v_j_4167_);
lean_dec_ref(v_as_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t v_sz_4169_, size_t v_i_4170_, lean_object* v_bs_4171_){
_start:
{
uint8_t v___x_4172_; 
v___x_4172_ = lean_usize_dec_lt(v_i_4170_, v_sz_4169_);
if (v___x_4172_ == 0)
{
return v_bs_4171_;
}
else
{
lean_object* v_v_4173_; lean_object* v___x_4174_; lean_object* v_bs_x27_4175_; lean_object* v___y_4177_; 
v_v_4173_ = lean_array_uget(v_bs_4171_, v_i_4170_);
v___x_4174_ = lean_unsigned_to_nat(0u);
v_bs_x27_4175_ = lean_array_uset(v_bs_4171_, v_i_4170_, v___x_4174_);
if (lean_obj_tag(v_v_4173_) == 0)
{
lean_object* v_doc_4182_; 
v_doc_4182_ = lean_ctor_get(v_v_4173_, 0);
lean_inc_ref(v_doc_4182_);
lean_dec_ref_known(v_v_4173_, 1);
v___y_4177_ = v_doc_4182_;
goto v___jp_4176_;
}
else
{
lean_object* v_docs_4183_; lean_object* v___x_4184_; 
v_docs_4183_ = lean_ctor_get(v_v_4173_, 0);
lean_inc_ref(v_docs_4183_);
lean_dec_ref_known(v_v_4173_, 1);
v___x_4184_ = l_Lean_Fmt_Layouts_fill(v_docs_4183_);
lean_dec_ref(v_docs_4183_);
v___y_4177_ = v___x_4184_;
goto v___jp_4176_;
}
v___jp_4176_:
{
size_t v___x_4178_; size_t v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = ((size_t)1ULL);
v___x_4179_ = lean_usize_add(v_i_4170_, v___x_4178_);
v___x_4180_ = lean_array_uset(v_bs_x27_4175_, v_i_4170_, v___y_4177_);
v_i_4170_ = v___x_4179_;
v_bs_4171_ = v___x_4180_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object* v_sz_4185_, lean_object* v_i_4186_, lean_object* v_bs_4187_){
_start:
{
size_t v_sz_boxed_4188_; size_t v_i_boxed_4189_; lean_object* v_res_4190_; 
v_sz_boxed_4188_ = lean_unbox_usize(v_sz_4185_);
lean_dec(v_sz_4185_);
v_i_boxed_4189_ = lean_unbox_usize(v_i_4186_);
lean_dec(v_i_4186_);
v_res_4190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_boxed_4188_, v_i_boxed_4189_, v_bs_4187_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object* v_lb_4192_, lean_object* v_terms_4193_, lean_object* v_rb_4194_){
_start:
{
lean_object* v_terms_4196_; size_t v_sz_4204_; size_t v___x_4205_; lean_object* v_terms_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; 
v_sz_4204_ = lean_array_size(v_terms_4193_);
v___x_4205_ = ((size_t)0ULL);
v_terms_4206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_4204_, v___x_4205_, v_terms_4193_);
v___x_4207_ = lean_unsigned_to_nat(1u);
v___x_4208_ = lean_array_get_size(v_terms_4206_);
v___x_4209_ = lean_nat_dec_lt(v___x_4207_, v___x_4208_);
if (v___x_4209_ == 0)
{
v_terms_4196_ = v_terms_4206_;
goto v___jp_4195_;
}
else
{
lean_object* v___x_4210_; lean_object* v_firstElemsIdx_x3f_4211_; 
v___x_4210_ = lean_unsigned_to_nat(0u);
v_firstElemsIdx_x3f_4211_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_terms_4206_, v___x_4210_);
if (lean_obj_tag(v_firstElemsIdx_x3f_4211_) == 1)
{
lean_object* v_val_4212_; uint8_t v___x_4213_; 
v_val_4212_ = lean_ctor_get(v_firstElemsIdx_x3f_4211_, 0);
lean_inc(v_val_4212_);
lean_dec_ref_known(v_firstElemsIdx_x3f_4211_, 1);
v___x_4213_ = lean_nat_dec_lt(v_val_4212_, v___x_4208_);
if (v___x_4213_ == 0)
{
lean_dec(v_val_4212_);
v_terms_4196_ = v_terms_4206_;
goto v___jp_4195_;
}
else
{
lean_object* v_v_4214_; lean_object* v___x_4215_; lean_object* v_xs_x27_4216_; lean_object* v___y_4218_; 
v_v_4214_ = lean_array_fget(v_terms_4206_, v_val_4212_);
v___x_4215_ = lean_box(0);
v_xs_x27_4216_ = lean_array_fset(v_terms_4206_, v_val_4212_, v___x_4215_);
if (lean_obj_tag(v_v_4214_) == 0)
{
v___y_4218_ = v_v_4214_;
goto v___jp_4217_;
}
else
{
lean_object* v_docs_4220_; lean_object* v___x_4221_; uint8_t v___x_4222_; 
v_docs_4220_ = lean_ctor_get(v_v_4214_, 0);
v___x_4221_ = lean_array_get_size(v_docs_4220_);
v___x_4222_ = lean_nat_dec_lt(v___x_4210_, v___x_4221_);
if (v___x_4222_ == 0)
{
v___y_4218_ = v_v_4214_;
goto v___jp_4217_;
}
else
{
lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4233_; 
lean_inc_ref(v_docs_4220_);
v_isSharedCheck_4233_ = !lean_is_exclusive(v_v_4214_);
if (v_isSharedCheck_4233_ == 0)
{
lean_object* v_unused_4234_; 
v_unused_4234_ = lean_ctor_get(v_v_4214_, 0);
lean_dec(v_unused_4234_);
v___x_4224_ = v_v_4214_;
v_isShared_4225_ = v_isSharedCheck_4233_;
goto v_resetjp_4223_;
}
else
{
lean_dec(v_v_4214_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4233_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v_v_4226_; lean_object* v_xs_x27_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4231_; 
v_v_4226_ = lean_array_fget(v_docs_4220_, v___x_4210_);
v_xs_x27_4227_ = lean_array_fset(v_docs_4220_, v___x_4210_, v___x_4215_);
v___x_4228_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4226_);
v___x_4229_ = lean_array_fset(v_xs_x27_4227_, v___x_4210_, v___x_4228_);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4229_);
v___x_4231_ = v___x_4224_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4229_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
v___y_4218_ = v___x_4231_;
goto v___jp_4217_;
}
}
}
}
v___jp_4217_:
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_array_fset(v_xs_x27_4216_, v_val_4212_, v___y_4218_);
lean_dec(v_val_4212_);
v_terms_4196_ = v___x_4219_;
goto v___jp_4195_;
}
}
}
else
{
lean_dec(v_firstElemsIdx_x3f_4211_);
v_terms_4196_ = v_terms_4206_;
goto v___jp_4195_;
}
}
v___jp_4195_:
{
lean_object* v___x_4197_; size_t v_sz_4198_; size_t v___x_4199_; lean_object* v_terms_x27_4200_; lean_object* v_terms_x27_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4197_ = ((lean_object*)(l_Lean_Fmt_Layouts_metaApplication___closed__0));
v_sz_4198_ = lean_array_size(v_terms_4196_);
v___x_4199_ = ((size_t)0ULL);
v_terms_x27_4200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_4198_, v___x_4199_, v_terms_4196_);
v_terms_x27_4201_ = l_Lean_Fmt_Layouts_sepFill(v___x_4197_, v_terms_x27_4200_);
lean_dec_ref(v_terms_x27_4200_);
v___x_4202_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4203_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4192_, v_terms_x27_4201_, v_rb_4194_, v___x_4202_);
return v___x_4203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object* v_chain_4237_){
_start:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
v___x_4238_ = ((lean_object*)(l_Lean_Fmt_Layouts_pipeOperator___closed__0));
v___x_4239_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_4237_, v___x_4238_);
return v___x_4239_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0(void){
_start:
{
uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4240_ = 1;
v___x_4241_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4242_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
lean_ctor_set_uint8(v___x_4242_, sizeof(void*)*1, v___x_4240_);
return v___x_4242_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default(void){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = lean_obj_once(&l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0, &l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0);
return v___x_4243_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock(void){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object* v_block_4245_){
_start:
{
uint8_t v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = 1;
v___x_4247_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4247_, 0, v_block_4245_);
lean_ctor_set_uint8(v___x_4247_, sizeof(void*)*1, v___x_4246_);
return v___x_4247_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object* v_val_4250_, uint8_t v___x_4251_, lean_object* v___x_4252_, lean_object* v_____r_4253_, lean_object* v_stickyAcc_4254_){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4255_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_4250_, v___x_4251_);
v___x_4256_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v___x_4252_, v_stickyAcc_4254_, v___x_4255_);
lean_dec(v___x_4255_);
v___x_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object* v_val_4258_, lean_object* v___x_4259_, lean_object* v___x_4260_, lean_object* v_____r_4261_, lean_object* v_stickyAcc_4262_){
_start:
{
uint8_t v___x_1444__boxed_4263_; lean_object* v_res_4264_; 
v___x_1444__boxed_4263_ = lean_unbox(v___x_4259_);
v_res_4264_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4258_, v___x_1444__boxed_4263_, v___x_4260_, v_____r_4261_, v_stickyAcc_4262_);
lean_dec_ref(v_val_4258_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object* v_upperBound_4265_, lean_object* v___y_4266_, lean_object* v___x_4267_, lean_object* v_a_4268_, lean_object* v_b_4269_){
_start:
{
uint8_t v___x_4270_; 
v___x_4270_ = lean_nat_dec_lt(v_a_4268_, v_upperBound_4265_);
if (v___x_4270_ == 0)
{
lean_dec(v_a_4268_);
return v_b_4269_;
}
else
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v_block_4273_; uint8_t v_hardNestedIfFirst_4274_; lean_object* v___x_4275_; lean_object* v_a_4277_; lean_object* v___y_4281_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4271_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4272_ = lean_array_get_borrowed(v___x_4271_, v___y_4266_, v_a_4268_);
v_block_4273_ = lean_ctor_get(v___x_4272_, 0);
v_hardNestedIfFirst_4274_ = lean_ctor_get_uint8(v___x_4272_, sizeof(void*)*1);
v___x_4275_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_b_4269_);
v___x_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4284_, 0, v_b_4269_);
v___x_4285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_4286_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4284_, v___x_4285_);
v___x_4287_ = lean_box(0);
lean_inc_ref_n(v_block_4273_, 2);
v___x_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4288_, 0, v_block_4273_);
v___x_4289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4287_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
lean_ctor_set(v___x_4289_, 2, v___x_4287_);
v___x_4290_ = lean_unsigned_to_nat(2u);
v___x_4291_ = lean_mk_empty_array_with_capacity(v___x_4290_);
lean_inc_ref(v___x_4291_);
v___x_4292_ = lean_array_push(v___x_4291_, v___x_4286_);
v___x_4293_ = lean_array_push(v___x_4292_, v___x_4289_);
v___x_4294_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4293_);
lean_dec_ref(v___x_4293_);
v___x_4295_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4294_);
v___x_4296_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_block_4273_);
if (lean_obj_tag(v___x_4296_) == 1)
{
lean_object* v_val_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4321_; 
v_val_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4321_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_val_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4321_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v_stickyVariant_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
v_stickyVariant_4301_ = lean_ctor_get(v_val_4297_, 0);
v___x_4302_ = l_Lean_Fmt_TaggedDoc_flattened(v_b_4269_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4302_);
v___x_4304_ = v___x_4299_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4305_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4306_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4304_, v___x_4305_);
lean_inc_ref(v_stickyVariant_4301_);
v___x_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4307_, 0, v_stickyVariant_4301_);
v___x_4308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4287_);
lean_ctor_set(v___x_4308_, 1, v___x_4307_);
lean_ctor_set(v___x_4308_, 2, v___x_4287_);
v___x_4309_ = lean_array_push(v___x_4291_, v___x_4306_);
v___x_4310_ = lean_array_push(v___x_4309_, v___x_4308_);
v___x_4311_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4310_);
lean_dec_ref(v___x_4310_);
if (v_hardNestedIfFirst_4274_ == 0)
{
goto v___jp_4312_;
}
else
{
lean_object* v___x_4315_; uint8_t v___x_4316_; 
v___x_4315_ = lean_nat_sub(v___x_4267_, v___x_4275_);
v___x_4316_ = lean_nat_dec_lt(v_a_4268_, v___x_4315_);
lean_dec(v___x_4315_);
if (v___x_4316_ == 0)
{
goto v___jp_4312_;
}
else
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4317_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_4311_);
v___x_4318_ = lean_box(0);
v___x_4319_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4297_, v___x_4270_, v___x_4295_, v___x_4318_, v___x_4317_);
lean_dec(v_val_4297_);
v___y_4281_ = v___x_4319_;
goto v___jp_4280_;
}
}
v___jp_4312_:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = lean_box(0);
v___x_4314_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4297_, v___x_4270_, v___x_4295_, v___x_4313_, v___x_4311_);
lean_dec(v_val_4297_);
v___y_4281_ = v___x_4314_;
goto v___jp_4280_;
}
}
}
}
else
{
lean_dec(v___x_4296_);
lean_dec_ref(v___x_4291_);
lean_dec_ref(v_b_4269_);
v_a_4277_ = v___x_4295_;
goto v___jp_4276_;
}
v___jp_4276_:
{
lean_object* v___x_4278_; 
v___x_4278_ = lean_nat_add(v_a_4268_, v___x_4275_);
lean_dec(v_a_4268_);
v_a_4268_ = v___x_4278_;
v_b_4269_ = v_a_4277_;
goto _start;
}
v___jp_4280_:
{
if (lean_obj_tag(v___y_4281_) == 0)
{
lean_object* v_a_4282_; 
lean_dec(v_a_4268_);
v_a_4282_ = lean_ctor_get(v___y_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___y_4281_, 1);
return v_a_4282_;
}
else
{
lean_object* v_a_4283_; 
v_a_4283_ = lean_ctor_get(v___y_4281_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___y_4281_, 1);
v_a_4277_ = v_a_4283_;
goto v___jp_4276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object* v_upperBound_4322_, lean_object* v___y_4323_, lean_object* v___x_4324_, lean_object* v_a_4325_, lean_object* v_b_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4322_, v___y_4323_, v___x_4324_, v_a_4325_, v_b_4326_);
lean_dec(v___x_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v_upperBound_4322_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object* v_as_4328_, size_t v_i_4329_, size_t v_stop_4330_, lean_object* v_b_4331_){
_start:
{
lean_object* v___y_4333_; uint8_t v___x_4337_; 
v___x_4337_ = lean_usize_dec_eq(v_i_4329_, v_stop_4330_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; lean_object* v_block_4339_; uint8_t v___x_4340_; 
v___x_4338_ = lean_array_uget_borrowed(v_as_4328_, v_i_4329_);
v_block_4339_ = lean_ctor_get(v___x_4338_, 0);
v___x_4340_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_block_4339_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4341_; 
lean_inc(v___x_4338_);
v___x_4341_ = lean_array_push(v_b_4331_, v___x_4338_);
v___y_4333_ = v___x_4341_;
goto v___jp_4332_;
}
else
{
v___y_4333_ = v_b_4331_;
goto v___jp_4332_;
}
}
else
{
return v_b_4331_;
}
v___jp_4332_:
{
size_t v___x_4334_; size_t v___x_4335_; 
v___x_4334_ = ((size_t)1ULL);
v___x_4335_ = lean_usize_add(v_i_4329_, v___x_4334_);
v_i_4329_ = v___x_4335_;
v_b_4331_ = v___y_4333_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object* v_as_4342_, lean_object* v_i_4343_, lean_object* v_stop_4344_, lean_object* v_b_4345_){
_start:
{
size_t v_i_boxed_4346_; size_t v_stop_boxed_4347_; lean_object* v_res_4348_; 
v_i_boxed_4346_ = lean_unbox_usize(v_i_4343_);
lean_dec(v_i_4343_);
v_stop_boxed_4347_ = lean_unbox_usize(v_stop_4344_);
lean_dec(v_stop_4344_);
v_res_4348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_as_4342_, v_i_boxed_4346_, v_stop_boxed_4347_, v_b_4345_);
lean_dec_ref(v_as_4342_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object* v_blocks_4351_, uint8_t v_format_4352_){
_start:
{
lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___y_4363_; lean_object* v___x_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v___x_4360_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4361_ = lean_unsigned_to_nat(0u);
v___x_4373_ = lean_array_get_size(v_blocks_4351_);
v___x_4374_ = ((lean_object*)(l_Lean_Fmt_Layouts_blocks___closed__0));
v___x_4375_ = lean_nat_dec_lt(v___x_4361_, v___x_4373_);
if (v___x_4375_ == 0)
{
v___y_4363_ = v___x_4374_;
goto v___jp_4362_;
}
else
{
uint8_t v___x_4376_; 
v___x_4376_ = lean_nat_dec_le(v___x_4373_, v___x_4373_);
if (v___x_4376_ == 0)
{
if (v___x_4375_ == 0)
{
v___y_4363_ = v___x_4374_;
goto v___jp_4362_;
}
else
{
size_t v___x_4377_; size_t v___x_4378_; lean_object* v___x_4379_; 
v___x_4377_ = ((size_t)0ULL);
v___x_4378_ = lean_usize_of_nat(v___x_4373_);
v___x_4379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4351_, v___x_4377_, v___x_4378_, v___x_4374_);
v___y_4363_ = v___x_4379_;
goto v___jp_4362_;
}
}
else
{
size_t v___x_4380_; size_t v___x_4381_; lean_object* v___x_4382_; 
v___x_4380_ = ((size_t)0ULL);
v___x_4381_ = lean_usize_of_nat(v___x_4373_);
v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4351_, v___x_4380_, v___x_4381_, v___x_4374_);
v___y_4363_ = v___x_4382_;
goto v___jp_4362_;
}
}
v___jp_4353_:
{
lean_object* v___x_4358_; 
v___x_4358_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v___y_4355_, v___y_4356_, v___y_4355_, v___y_4354_, v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec(v___y_4355_);
if (v_format_4352_ == 0)
{
return v___x_4358_;
}
else
{
lean_object* v___x_4359_; 
v___x_4359_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4358_);
return v___x_4359_;
}
}
v___jp_4362_:
{
lean_object* v___x_4364_; uint8_t v___x_4365_; 
v___x_4364_ = lean_array_get_size(v___y_4363_);
v___x_4365_ = lean_nat_dec_eq(v___x_4364_, v___x_4361_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; lean_object* v_block_4367_; uint8_t v_hardNestedIfFirst_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; 
v___x_4366_ = lean_array_get_borrowed(v___x_4360_, v___y_4363_, v___x_4361_);
v_block_4367_ = lean_ctor_get(v___x_4366_, 0);
v_hardNestedIfFirst_4368_ = lean_ctor_get_uint8(v___x_4366_, sizeof(void*)*1);
v___x_4369_ = lean_unsigned_to_nat(1u);
v___x_4370_ = lean_nat_dec_eq(v___x_4364_, v___x_4369_);
if (v___x_4370_ == 0)
{
if (v_hardNestedIfFirst_4368_ == 0)
{
lean_inc_ref(v_block_4367_);
v___y_4354_ = v___x_4369_;
v___y_4355_ = v___x_4364_;
v___y_4356_ = v___y_4363_;
v___y_4357_ = v_block_4367_;
goto v___jp_4353_;
}
else
{
lean_object* v___x_4371_; 
lean_inc_ref(v_block_4367_);
v___x_4371_ = l_Lean_Fmt_TaggedDoc_hardNested(v_block_4367_);
v___y_4354_ = v___x_4369_;
v___y_4355_ = v___x_4364_;
v___y_4356_ = v___y_4363_;
v___y_4357_ = v___x_4371_;
goto v___jp_4353_;
}
}
else
{
lean_inc_ref(v_block_4367_);
lean_dec_ref(v___y_4363_);
return v_block_4367_;
}
}
else
{
lean_object* v___x_4372_; 
lean_dec_ref(v___y_4363_);
v___x_4372_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_4372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object* v_blocks_4383_, lean_object* v_format_4384_){
_start:
{
uint8_t v_format_boxed_4385_; lean_object* v_res_4386_; 
v_format_boxed_4385_ = lean_unbox(v_format_4384_);
v_res_4386_ = l_Lean_Fmt_Layouts_blocks(v_blocks_4383_, v_format_boxed_4385_);
lean_dec_ref(v_blocks_4383_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object* v_upperBound_4387_, lean_object* v___y_4388_, lean_object* v___x_4389_, lean_object* v_inst_4390_, lean_object* v_R_4391_, lean_object* v_a_4392_, lean_object* v_b_4393_, lean_object* v_c_4394_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4387_, v___y_4388_, v___x_4389_, v_a_4392_, v_b_4393_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object* v_upperBound_4396_, lean_object* v___y_4397_, lean_object* v___x_4398_, lean_object* v_inst_4399_, lean_object* v_R_4400_, lean_object* v_a_4401_, lean_object* v_b_4402_, lean_object* v_c_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(v_upperBound_4396_, v___y_4397_, v___x_4398_, v_inst_4399_, v_R_4400_, v_a_4401_, v_b_4402_, v_c_4403_);
lean_dec(v___x_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v_upperBound_4396_);
return v_res_4404_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_tuple___closed__0(void){
_start:
{
uint8_t v___x_4405_; uint8_t v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4405_ = 0;
v___x_4406_ = 1;
v___x_4407_ = l_Lean_Fmt_TaggedDoc_break;
v___x_4408_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
lean_ctor_set_uint8(v___x_4408_, sizeof(void*)*1, v___x_4406_);
lean_ctor_set_uint8(v___x_4408_, sizeof(void*)*1 + 1, v___x_4405_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object* v_sep_4409_, lean_object* v_lb_4410_, lean_object* v_fields_4411_, lean_object* v_rb_4412_){
_start:
{
uint8_t v___x_4413_; lean_object* v_fields_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v___x_4413_ = 1;
lean_inc_ref(v_sep_4409_);
v_fields_4414_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4409_, v_fields_4411_, v___x_4413_);
v___x_4415_ = lean_array_get_size(v_fields_4414_);
v___x_4416_ = lean_unsigned_to_nat(1u);
v___x_4417_ = lean_nat_dec_eq(v___x_4415_, v___x_4416_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; lean_object* v_fields_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4418_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v_fields_4419_ = l_Lean_Fmt_Layouts_sepArray(v_sep_4409_, v_fields_4414_, v___x_4418_);
lean_dec_ref(v_fields_4414_);
v___x_4420_ = lean_obj_once(&l_Lean_Fmt_Layouts_tuple___closed__0, &l_Lean_Fmt_Layouts_tuple___closed__0_once, _init_l_Lean_Fmt_Layouts_tuple___closed__0);
v___x_4421_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4410_, v_fields_4419_, v_rb_4412_, v___x_4420_);
return v___x_4421_;
}
else
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
lean_dec_ref(v_sep_4409_);
v___x_4422_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4423_ = lean_unsigned_to_nat(0u);
v___x_4424_ = lean_array_get(v___x_4422_, v_fields_4414_, v___x_4423_);
lean_dec_ref(v_fields_4414_);
v___x_4425_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4426_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4410_, v___x_4424_, v_rb_4412_, v___x_4425_);
return v___x_4426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object* v_sep_4427_, lean_object* v_lb_4428_, lean_object* v_fields_4429_, lean_object* v_rb_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_Fmt_Layouts_tuple(v_sep_4427_, v_lb_4428_, v_fields_4429_, v_rb_4430_);
lean_dec_ref(v_fields_4429_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object* v_sep_4432_, lean_object* v_lb_4433_, lean_object* v_elems_4434_, lean_object* v_rb_4435_, lean_object* v_format_4436_){
_start:
{
uint8_t v_spacing_4437_; uint8_t v_unindentedRb_4438_; uint8_t v___x_4439_; lean_object* v_elems_4440_; lean_object* v___y_4442_; 
v_spacing_4437_ = lean_ctor_get_uint8(v_format_4436_, 0);
v_unindentedRb_4438_ = lean_ctor_get_uint8(v_format_4436_, 1);
v___x_4439_ = 1;
lean_inc_ref(v_sep_4432_);
v_elems_4440_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4432_, v_elems_4434_, v___x_4439_);
if (v_spacing_4437_ == 0)
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_Fmt_TaggedDoc_break;
v___y_4442_ = v___x_4447_;
goto v___jp_4441_;
}
else
{
lean_object* v___x_4448_; 
v___x_4448_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4442_ = v___x_4448_;
goto v___jp_4441_;
}
v___jp_4441_:
{
lean_object* v_fields_4443_; uint8_t v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_fields_4443_ = l_Lean_Fmt_Layouts_sepFill(v_sep_4432_, v_elems_4440_);
lean_dec_ref(v_elems_4440_);
v___x_4444_ = 1;
lean_inc_ref(v___y_4442_);
v___x_4445_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4445_, 0, v___y_4442_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*1, v_unindentedRb_4438_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*1 + 1, v___x_4444_);
v___x_4446_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4433_, v_fields_4443_, v_rb_4435_, v___x_4445_);
return v___x_4446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object* v_sep_4449_, lean_object* v_lb_4450_, lean_object* v_elems_4451_, lean_object* v_rb_4452_, lean_object* v_format_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_Fmt_Layouts_collection(v_sep_4449_, v_lb_4450_, v_elems_4451_, v_rb_4452_, v_format_4453_);
lean_dec_ref(v_format_4453_);
lean_dec_ref(v_elems_4451_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object* v_keyword_4455_, lean_object* v_collection_4456_){
_start:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v___x_4457_ = lean_unsigned_to_nat(2u);
v___x_4458_ = lean_mk_empty_array_with_capacity(v___x_4457_);
v___x_4459_ = lean_array_push(v___x_4458_, v_keyword_4455_);
v___x_4460_ = lean_array_push(v___x_4459_, v_collection_4456_);
v___x_4461_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4460_);
lean_dec_ref(v___x_4460_);
v___x_4462_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4461_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object* v_sep_4463_, lean_object* v_keyword_4464_, lean_object* v_lb_4465_, lean_object* v_elems_4466_, lean_object* v_rb_4467_, lean_object* v_format_4468_){
_start:
{
lean_object* v___f_4469_; lean_object* v_collection_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___f_4469_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0), 2, 1);
lean_closure_set(v___f_4469_, 0, v_keyword_4464_);
v_collection_4470_ = l_Lean_Fmt_Layouts_collection(v_sep_4463_, v_lb_4465_, v_elems_4466_, v_rb_4467_, v_format_4468_);
v___x_4471_ = lean_box(0);
v___x_4472_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_collection_4470_, v___f_4469_, v___x_4471_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object* v_sep_4473_, lean_object* v_keyword_4474_, lean_object* v_lb_4475_, lean_object* v_elems_4476_, lean_object* v_rb_4477_, lean_object* v_format_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_Fmt_Layouts_keywordPrefixedCollection(v_sep_4473_, v_keyword_4474_, v_lb_4475_, v_elems_4476_, v_rb_4477_, v_format_4478_);
lean_dec_ref(v_format_4478_);
lean_dec_ref(v_elems_4476_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(lean_object* v_x_4480_){
_start:
{
if (lean_obj_tag(v_x_4480_) == 0)
{
lean_object* v___x_4481_; 
v___x_4481_ = lean_unsigned_to_nat(0u);
return v___x_4481_;
}
else
{
lean_object* v___x_4482_; 
v___x_4482_ = lean_unsigned_to_nat(1u);
return v___x_4482_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___boxed(lean_object* v_x_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(v_x_4483_);
lean_dec(v_x_4483_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object* v_t_4485_, lean_object* v_k_4486_){
_start:
{
if (lean_obj_tag(v_t_4485_) == 0)
{
uint8_t v_respectPseudoAlignment_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v_respectPseudoAlignment_4487_ = lean_ctor_get_uint8(v_t_4485_, 0);
v___x_4488_ = lean_box(v_respectPseudoAlignment_4487_);
v___x_4489_ = lean_apply_1(v_k_4486_, v___x_4488_);
return v___x_4489_;
}
else
{
return v_k_4486_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object* v_t_4490_, lean_object* v_k_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4490_, v_k_4491_);
lean_dec(v_t_4490_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object* v_motive_4493_, lean_object* v_ctorIdx_4494_, lean_object* v_t_4495_, lean_object* v_h_4496_, lean_object* v_k_4497_){
_start:
{
lean_object* v___x_4498_; 
v___x_4498_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4495_, v_k_4497_);
return v___x_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object* v_motive_4499_, lean_object* v_ctorIdx_4500_, lean_object* v_t_4501_, lean_object* v_h_4502_, lean_object* v_k_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(v_motive_4499_, v_ctorIdx_4500_, v_t_4501_, v_h_4502_, v_k_4503_);
lean_dec(v_t_4501_);
lean_dec(v_ctorIdx_4500_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object* v_t_4505_, lean_object* v_local_4506_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4505_, v_local_4506_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object* v_t_4508_, lean_object* v_local_4509_){
_start:
{
lean_object* v_res_4510_; 
v_res_4510_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(v_t_4508_, v_local_4509_);
lean_dec(v_t_4508_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object* v_motive_4511_, lean_object* v_t_4512_, lean_object* v_h_4513_, lean_object* v_local_4514_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4512_, v_local_4514_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object* v_motive_4516_, lean_object* v_t_4517_, lean_object* v_h_4518_, lean_object* v_local_4519_){
_start:
{
lean_object* v_res_4520_; 
v_res_4520_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(v_motive_4516_, v_t_4517_, v_h_4518_, v_local_4519_);
lean_dec(v_t_4517_);
return v_res_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object* v_t_4521_, lean_object* v_global_4522_){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4521_, v_global_4522_);
return v___x_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object* v_t_4524_, lean_object* v_global_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(v_t_4524_, v_global_4525_);
lean_dec(v_t_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object* v_motive_4527_, lean_object* v_t_4528_, lean_object* v_h_4529_, lean_object* v_global_4530_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_t_4528_, v_global_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object* v_motive_4532_, lean_object* v_t_4533_, lean_object* v_h_4534_, lean_object* v_global_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(v_motive_4532_, v_t_4533_, v_h_4534_, v_global_4535_);
lean_dec(v_t_4533_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(lean_object* v_as_4537_, size_t v_i_4538_, size_t v_stop_4539_, lean_object* v_b_4540_){
_start:
{
lean_object* v___y_4542_; uint8_t v___x_4546_; 
v___x_4546_ = lean_usize_dec_eq(v_i_4538_, v_stop_4539_);
if (v___x_4546_ == 0)
{
lean_object* v___x_4547_; lean_object* v___y_4549_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; uint8_t v___x_4556_; 
v___x_4547_ = lean_unsigned_to_nat(0u);
v___x_4553_ = lean_array_uget_borrowed(v_as_4537_, v_i_4538_);
v___x_4554_ = lean_array_get_size(v___x_4553_);
v___x_4555_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4556_ = lean_nat_dec_lt(v___x_4547_, v___x_4554_);
if (v___x_4556_ == 0)
{
v___y_4549_ = v___x_4555_;
goto v___jp_4548_;
}
else
{
uint8_t v___x_4557_; 
v___x_4557_ = lean_nat_dec_le(v___x_4554_, v___x_4554_);
if (v___x_4557_ == 0)
{
if (v___x_4556_ == 0)
{
v___y_4549_ = v___x_4555_;
goto v___jp_4548_;
}
else
{
size_t v___x_4558_; size_t v___x_4559_; lean_object* v___x_4560_; 
v___x_4558_ = ((size_t)0ULL);
v___x_4559_ = lean_usize_of_nat(v___x_4554_);
v___x_4560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v___x_4553_, v___x_4558_, v___x_4559_, v___x_4555_);
v___y_4549_ = v___x_4560_;
goto v___jp_4548_;
}
}
else
{
size_t v___x_4561_; size_t v___x_4562_; lean_object* v___x_4563_; 
v___x_4561_ = ((size_t)0ULL);
v___x_4562_ = lean_usize_of_nat(v___x_4554_);
v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v___x_4553_, v___x_4561_, v___x_4562_, v___x_4555_);
v___y_4549_ = v___x_4563_;
goto v___jp_4548_;
}
}
v___jp_4548_:
{
lean_object* v___x_4550_; uint8_t v___x_4551_; 
v___x_4550_ = lean_array_get_size(v___y_4549_);
v___x_4551_ = lean_nat_dec_eq(v___x_4550_, v___x_4547_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; 
v___x_4552_ = lean_array_push(v_b_4540_, v___y_4549_);
v___y_4542_ = v___x_4552_;
goto v___jp_4541_;
}
else
{
lean_dec_ref(v___y_4549_);
v___y_4542_ = v_b_4540_;
goto v___jp_4541_;
}
}
}
else
{
return v_b_4540_;
}
v___jp_4541_:
{
size_t v___x_4543_; size_t v___x_4544_; 
v___x_4543_ = ((size_t)1ULL);
v___x_4544_ = lean_usize_add(v_i_4538_, v___x_4543_);
v_i_4538_ = v___x_4544_;
v_b_4540_ = v___y_4542_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0___boxed(lean_object* v_as_4564_, lean_object* v_i_4565_, lean_object* v_stop_4566_, lean_object* v_b_4567_){
_start:
{
size_t v_i_boxed_4568_; size_t v_stop_boxed_4569_; lean_object* v_res_4570_; 
v_i_boxed_4568_ = lean_unbox_usize(v_i_4565_);
lean_dec(v_i_4565_);
v_stop_boxed_4569_ = lean_unbox_usize(v_stop_4566_);
lean_dec(v_stop_4566_);
v_res_4570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(v_as_4564_, v_i_boxed_4568_, v_stop_boxed_4569_, v_b_4567_);
lean_dec_ref(v_as_4564_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object* v_as_4573_, lean_object* v_start_4574_, lean_object* v_stop_4575_){
_start:
{
lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4576_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___closed__0));
v___x_4577_ = lean_nat_dec_lt(v_start_4574_, v_stop_4575_);
if (v___x_4577_ == 0)
{
return v___x_4576_;
}
else
{
lean_object* v___x_4578_; uint8_t v___x_4579_; 
v___x_4578_ = lean_array_get_size(v_as_4573_);
v___x_4579_ = lean_nat_dec_le(v_stop_4575_, v___x_4578_);
if (v___x_4579_ == 0)
{
uint8_t v___x_4580_; 
v___x_4580_ = lean_nat_dec_lt(v_start_4574_, v___x_4578_);
if (v___x_4580_ == 0)
{
return v___x_4576_;
}
else
{
size_t v___x_4581_; size_t v___x_4582_; lean_object* v___x_4583_; 
v___x_4581_ = lean_usize_of_nat(v_start_4574_);
v___x_4582_ = lean_usize_of_nat(v___x_4578_);
v___x_4583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(v_as_4573_, v___x_4581_, v___x_4582_, v___x_4576_);
return v___x_4583_;
}
}
else
{
size_t v___x_4584_; size_t v___x_4585_; lean_object* v___x_4586_; 
v___x_4584_ = lean_usize_of_nat(v_start_4574_);
v___x_4585_ = lean_usize_of_nat(v_stop_4575_);
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(v_as_4573_, v___x_4584_, v___x_4585_, v___x_4576_);
return v___x_4586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object* v_as_4587_, lean_object* v_start_4588_, lean_object* v_stop_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_as_4587_, v_start_4588_, v_stop_4589_);
lean_dec(v_stop_4589_);
lean_dec(v_start_4588_);
lean_dec_ref(v_as_4587_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(lean_object* v_as_4591_, size_t v_i_4592_, size_t v_stop_4593_, lean_object* v_b_4594_){
_start:
{
lean_object* v___y_4596_; uint8_t v___x_4600_; 
v___x_4600_ = lean_usize_dec_eq(v_i_4592_, v_stop_4593_);
if (v___x_4600_ == 0)
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v_group_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; 
v___x_4601_ = lean_unsigned_to_nat(0u);
v___x_4602_ = lean_array_uget_borrowed(v_as_4591_, v_i_4592_);
v___x_4603_ = lean_array_get_size(v___x_4602_);
v_group_4604_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v___x_4602_, v___x_4601_, v___x_4603_);
v___x_4605_ = lean_array_get_size(v_group_4604_);
v___x_4606_ = lean_nat_dec_eq(v___x_4605_, v___x_4601_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; 
v___x_4607_ = lean_array_push(v_b_4594_, v_group_4604_);
v___y_4596_ = v___x_4607_;
goto v___jp_4595_;
}
else
{
lean_dec_ref(v_group_4604_);
v___y_4596_ = v_b_4594_;
goto v___jp_4595_;
}
}
else
{
return v_b_4594_;
}
v___jp_4595_:
{
size_t v___x_4597_; size_t v___x_4598_; 
v___x_4597_ = ((size_t)1ULL);
v___x_4598_ = lean_usize_add(v_i_4592_, v___x_4597_);
v_i_4592_ = v___x_4598_;
v_b_4594_ = v___y_4596_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2___boxed(lean_object* v_as_4608_, lean_object* v_i_4609_, lean_object* v_stop_4610_, lean_object* v_b_4611_){
_start:
{
size_t v_i_boxed_4612_; size_t v_stop_boxed_4613_; lean_object* v_res_4614_; 
v_i_boxed_4612_ = lean_unbox_usize(v_i_4609_);
lean_dec(v_i_4609_);
v_stop_boxed_4613_ = lean_unbox_usize(v_stop_4610_);
lean_dec(v_stop_4610_);
v_res_4614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(v_as_4608_, v_i_boxed_4612_, v_stop_boxed_4613_, v_b_4611_);
lean_dec_ref(v_as_4608_);
return v_res_4614_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object* v_as_4617_, lean_object* v_start_4618_, lean_object* v_stop_4619_){
_start:
{
lean_object* v___x_4620_; uint8_t v___x_4621_; 
v___x_4620_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0));
v___x_4621_ = lean_nat_dec_lt(v_start_4618_, v_stop_4619_);
if (v___x_4621_ == 0)
{
return v___x_4620_;
}
else
{
lean_object* v___x_4622_; uint8_t v___x_4623_; 
v___x_4622_ = lean_array_get_size(v_as_4617_);
v___x_4623_ = lean_nat_dec_le(v_stop_4619_, v___x_4622_);
if (v___x_4623_ == 0)
{
uint8_t v___x_4624_; 
v___x_4624_ = lean_nat_dec_lt(v_start_4618_, v___x_4622_);
if (v___x_4624_ == 0)
{
return v___x_4620_;
}
else
{
size_t v___x_4625_; size_t v___x_4626_; lean_object* v___x_4627_; 
v___x_4625_ = lean_usize_of_nat(v_start_4618_);
v___x_4626_ = lean_usize_of_nat(v___x_4622_);
v___x_4627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(v_as_4617_, v___x_4625_, v___x_4626_, v___x_4620_);
return v___x_4627_;
}
}
else
{
size_t v___x_4628_; size_t v___x_4629_; lean_object* v___x_4630_; 
v___x_4628_ = lean_usize_of_nat(v_start_4618_);
v___x_4629_ = lean_usize_of_nat(v_stop_4619_);
v___x_4630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(v_as_4617_, v___x_4628_, v___x_4629_, v___x_4620_);
return v___x_4630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object* v_as_4631_, lean_object* v_start_4632_, lean_object* v_stop_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_as_4631_, v_start_4632_, v_stop_4633_);
lean_dec(v_stop_4633_);
lean_dec(v_start_4632_);
lean_dec_ref(v_as_4631_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(size_t v_sz_4635_, size_t v_i_4636_, lean_object* v_bs_4637_){
_start:
{
uint8_t v___x_4638_; 
v___x_4638_ = lean_usize_dec_lt(v_i_4636_, v_sz_4635_);
if (v___x_4638_ == 0)
{
return v_bs_4637_;
}
else
{
lean_object* v_v_4639_; lean_object* v___x_4640_; lean_object* v_bs_x27_4641_; lean_object* v___x_4642_; size_t v___x_4643_; size_t v___x_4644_; lean_object* v___x_4645_; 
v_v_4639_ = lean_array_uget(v_bs_4637_, v_i_4636_);
v___x_4640_ = lean_unsigned_to_nat(0u);
v_bs_x27_4641_ = lean_array_uset(v_bs_4637_, v_i_4636_, v___x_4640_);
v___x_4642_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(v_v_4639_);
v___x_4643_ = ((size_t)1ULL);
v___x_4644_ = lean_usize_add(v_i_4636_, v___x_4643_);
v___x_4645_ = lean_array_uset(v_bs_x27_4641_, v_i_4636_, v___x_4642_);
v_i_4636_ = v___x_4644_;
v_bs_4637_ = v___x_4645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object* v_sz_4647_, lean_object* v_i_4648_, lean_object* v_bs_4649_){
_start:
{
size_t v_sz_boxed_4650_; size_t v_i_boxed_4651_; lean_object* v_res_4652_; 
v_sz_boxed_4650_ = lean_unbox_usize(v_sz_4647_);
lean_dec(v_sz_4647_);
v_i_boxed_4651_ = lean_unbox_usize(v_i_4648_);
lean_dec(v_i_4648_);
v_res_4652_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_sz_boxed_4650_, v_i_boxed_4651_, v_bs_4649_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object* v_lvals_4653_, lean_object* v_binderGroups_4654_, lean_object* v_typeAscriptionTk_4655_, lean_object* v_type_4656_, lean_object* v_kind_4657_, lean_object* v_lvalsLayout_4658_){
_start:
{
lean_object* v___y_4660_; lean_object* v___y_4661_; uint8_t v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4677_; uint8_t v___y_4678_; lean_object* v___y_4679_; lean_object* v___x_4685_; lean_object* v___y_4687_; lean_object* v___y_4688_; uint8_t v___y_4689_; lean_object* v___y_4699_; lean_object* v___x_4709_; lean_object* v___x_4710_; uint8_t v___x_4711_; 
v___x_4685_ = lean_unsigned_to_nat(0u);
v___x_4709_ = lean_array_get_size(v_lvals_4653_);
v___x_4710_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4711_ = lean_nat_dec_lt(v___x_4685_, v___x_4709_);
if (v___x_4711_ == 0)
{
v___y_4699_ = v___x_4710_;
goto v___jp_4698_;
}
else
{
uint8_t v___x_4712_; 
v___x_4712_ = lean_nat_dec_le(v___x_4709_, v___x_4709_);
if (v___x_4712_ == 0)
{
if (v___x_4711_ == 0)
{
v___y_4699_ = v___x_4710_;
goto v___jp_4698_;
}
else
{
size_t v___x_4713_; size_t v___x_4714_; lean_object* v___x_4715_; 
v___x_4713_ = ((size_t)0ULL);
v___x_4714_ = lean_usize_of_nat(v___x_4709_);
v___x_4715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_lvals_4653_, v___x_4713_, v___x_4714_, v___x_4710_);
v___y_4699_ = v___x_4715_;
goto v___jp_4698_;
}
}
else
{
size_t v___x_4716_; size_t v___x_4717_; lean_object* v___x_4718_; 
v___x_4716_ = ((size_t)0ULL);
v___x_4717_ = lean_usize_of_nat(v___x_4709_);
v___x_4718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_lvals_4653_, v___x_4716_, v___x_4717_, v___x_4710_);
v___y_4699_ = v___x_4718_;
goto v___jp_4698_;
}
}
v___jp_4659_:
{
size_t v_sz_4664_; size_t v___x_4665_; lean_object* v___x_4666_; lean_object* v_binderGroups_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; 
v_sz_4664_ = lean_array_size(v___y_4660_);
v___x_4665_ = ((size_t)0ULL);
v___x_4666_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_sz_4664_, v___x_4665_, v___y_4660_);
v_binderGroups_4667_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4666_, v___y_4662_);
lean_dec_ref(v___x_4666_);
v___x_4668_ = lean_apply_1(v_lvalsLayout_4658_, v___y_4661_);
v___x_4669_ = lean_unsigned_to_nat(2u);
v___x_4670_ = lean_mk_empty_array_with_capacity(v___x_4669_);
v___x_4671_ = lean_array_push(v___x_4670_, v___x_4668_);
v___x_4672_ = lean_array_push(v___x_4671_, v_binderGroups_4667_);
v___x_4673_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4672_, v___y_4662_);
lean_dec_ref(v___x_4672_);
v___x_4674_ = l_Lean_Fmt_Layouts_typeAscription(v___x_4673_, v_typeAscriptionTk_4655_, v_type_4656_, v___y_4663_);
lean_dec_ref(v___y_4663_);
v___x_4675_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4674_);
return v___x_4675_;
}
v___jp_4676_:
{
if (lean_obj_tag(v_kind_4657_) == 0)
{
uint8_t v_respectPseudoAlignment_4680_; uint8_t v___x_4681_; lean_object* v___x_4682_; 
v_respectPseudoAlignment_4680_ = lean_ctor_get_uint8(v_kind_4657_, 0);
v___x_4681_ = 0;
v___x_4682_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_4682_, 0, v___x_4681_);
lean_ctor_set_uint8(v___x_4682_, 1, v___x_4681_);
lean_ctor_set_uint8(v___x_4682_, 2, v___y_4678_);
lean_ctor_set_uint8(v___x_4682_, 3, v_respectPseudoAlignment_4680_);
v___y_4660_ = v___y_4677_;
v___y_4661_ = v___y_4679_;
v___y_4662_ = v___y_4678_;
v___y_4663_ = v___x_4682_;
goto v___jp_4659_;
}
else
{
uint8_t v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = 0;
v___x_4684_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_4684_, 0, v___x_4683_);
lean_ctor_set_uint8(v___x_4684_, 1, v___x_4683_);
lean_ctor_set_uint8(v___x_4684_, 2, v___y_4678_);
lean_ctor_set_uint8(v___x_4684_, 3, v___x_4683_);
lean_ctor_set_uint8(v___x_4684_, 4, v___x_4683_);
v___y_4660_ = v___y_4677_;
v___y_4661_ = v___y_4679_;
v___y_4662_ = v___y_4678_;
v___y_4663_ = v___x_4684_;
goto v___jp_4659_;
}
}
v___jp_4686_:
{
uint8_t v___x_4690_; 
v___x_4690_ = 1;
if (v___y_4689_ == 0)
{
lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4691_ = lean_array_get_size(v___y_4687_);
v___x_4692_ = lean_nat_dec_lt(v___x_4685_, v___x_4691_);
if (v___x_4692_ == 0)
{
v___y_4677_ = v___y_4688_;
v___y_4678_ = v___x_4690_;
v___y_4679_ = v___y_4687_;
goto v___jp_4676_;
}
else
{
lean_object* v_v_4693_; lean_object* v___x_4694_; lean_object* v_xs_x27_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v_v_4693_ = lean_array_fget(v___y_4687_, v___x_4685_);
v___x_4694_ = lean_box(0);
v_xs_x27_4695_ = lean_array_fset(v___y_4687_, v___x_4685_, v___x_4694_);
v___x_4696_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4693_);
v___x_4697_ = lean_array_fset(v_xs_x27_4695_, v___x_4685_, v___x_4696_);
v___y_4677_ = v___y_4688_;
v___y_4678_ = v___x_4690_;
v___y_4679_ = v___x_4697_;
goto v___jp_4676_;
}
}
else
{
v___y_4677_ = v___y_4688_;
v___y_4678_ = v___x_4690_;
v___y_4679_ = v___y_4687_;
goto v___jp_4676_;
}
}
v___jp_4698_:
{
lean_object* v___x_4700_; lean_object* v_binderGroups_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; uint8_t v___x_4704_; 
v___x_4700_ = lean_array_get_size(v_binderGroups_4654_);
v_binderGroups_4701_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_binderGroups_4654_, v___x_4685_, v___x_4700_);
v___x_4702_ = lean_array_get_size(v___y_4699_);
v___x_4703_ = lean_unsigned_to_nat(1u);
v___x_4704_ = lean_nat_dec_le(v___x_4702_, v___x_4703_);
if (v___x_4704_ == 0)
{
v___y_4687_ = v___y_4699_;
v___y_4688_ = v_binderGroups_4701_;
v___y_4689_ = v___x_4704_;
goto v___jp_4686_;
}
else
{
uint8_t v___x_4705_; 
v___x_4705_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_type_4656_);
if (v___x_4705_ == 0)
{
v___y_4687_ = v___y_4699_;
v___y_4688_ = v_binderGroups_4701_;
v___y_4689_ = v___x_4705_;
goto v___jp_4686_;
}
else
{
uint8_t v___x_4706_; 
v___x_4706_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_typeAscriptionTk_4655_);
if (v___x_4706_ == 0)
{
v___y_4687_ = v___y_4699_;
v___y_4688_ = v_binderGroups_4701_;
v___y_4689_ = v___x_4706_;
goto v___jp_4686_;
}
else
{
lean_object* v___x_4707_; uint8_t v___x_4708_; 
v___x_4707_ = lean_array_get_size(v_binderGroups_4701_);
v___x_4708_ = lean_nat_dec_eq(v___x_4707_, v___x_4685_);
v___y_4687_ = v___y_4699_;
v___y_4688_ = v_binderGroups_4701_;
v___y_4689_ = v___x_4708_;
goto v___jp_4686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object* v_lvals_4719_, lean_object* v_binderGroups_4720_, lean_object* v_typeAscriptionTk_4721_, lean_object* v_type_4722_, lean_object* v_kind_4723_, lean_object* v_lvalsLayout_4724_){
_start:
{
lean_object* v_res_4725_; 
v_res_4725_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4719_, v_binderGroups_4720_, v_typeAscriptionTk_4721_, v_type_4722_, v_kind_4723_, v_lvalsLayout_4724_);
lean_dec(v_kind_4723_);
lean_dec_ref(v_binderGroups_4720_);
lean_dec_ref(v_lvals_4719_);
return v_res_4725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(uint8_t v___x_4726_, lean_object* v_terms_4727_){
_start:
{
lean_object* v___x_4728_; 
v___x_4728_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4727_, v___x_4726_);
return v___x_4728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object* v___x_4729_, lean_object* v_terms_4730_){
_start:
{
uint8_t v___x_9__boxed_4731_; lean_object* v_res_4732_; 
v___x_9__boxed_4731_ = lean_unbox(v___x_4729_);
v_res_4732_ = l_Lean_Fmt_Layouts_localSignature___lam__0(v___x_9__boxed_4731_, v_terms_4730_);
lean_dec_ref(v_terms_4730_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object* v_lvals_4738_, lean_object* v_binderGroups_4739_, lean_object* v_typeAscriptionTk_4740_, lean_object* v_type_4741_){
_start:
{
lean_object* v___f_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___f_4742_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4743_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__1));
v___x_4744_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4738_, v_binderGroups_4739_, v_typeAscriptionTk_4740_, v_type_4741_, v___x_4743_, v___f_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object* v_lvals_4745_, lean_object* v_binderGroups_4746_, lean_object* v_typeAscriptionTk_4747_, lean_object* v_type_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l_Lean_Fmt_Layouts_localSignature(v_lvals_4745_, v_binderGroups_4746_, v_typeAscriptionTk_4747_, v_type_4748_);
lean_dec_ref(v_binderGroups_4746_);
lean_dec_ref(v_lvals_4745_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0(lean_object* v_terms_4750_){
_start:
{
uint8_t v___x_4751_; lean_object* v___x_4752_; 
v___x_4751_ = 1;
v___x_4752_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4750_, v___x_4751_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___lam__0___boxed(lean_object* v_terms_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Lean_Fmt_Layouts_globalSignature___lam__0(v_terms_4753_);
lean_dec_ref(v_terms_4753_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object* v_lvals_4756_, lean_object* v_binderGroups_4757_, lean_object* v_typeAscriptionTk_4758_, lean_object* v_type_4759_){
_start:
{
lean_object* v___f_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___f_4760_ = ((lean_object*)(l_Lean_Fmt_Layouts_globalSignature___closed__0));
v___x_4761_ = lean_box(1);
v___x_4762_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4756_, v_binderGroups_4757_, v_typeAscriptionTk_4758_, v_type_4759_, v___x_4761_, v___f_4760_);
return v___x_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object* v_lvals_4763_, lean_object* v_binderGroups_4764_, lean_object* v_typeAscriptionTk_4765_, lean_object* v_type_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Fmt_Layouts_globalSignature(v_lvals_4763_, v_binderGroups_4764_, v_typeAscriptionTk_4765_, v_type_4766_);
lean_dec_ref(v_binderGroups_4764_);
lean_dec_ref(v_lvals_4763_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object* v_signature_4768_, lean_object* v_separationTk_4769_, lean_object* v_body_4770_, uint8_t v_sticky_4771_){
_start:
{
uint8_t v___y_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; uint8_t v___y_4777_; uint8_t v___y_4781_; lean_object* v___y_4782_; uint8_t v___y_4806_; uint8_t v___x_4822_; 
v___x_4822_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_separationTk_4769_);
if (v___x_4822_ == 0)
{
v___y_4806_ = v___x_4822_;
goto v___jp_4805_;
}
else
{
uint8_t v___x_4823_; 
v___x_4823_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4770_);
v___y_4806_ = v___x_4823_;
goto v___jp_4805_;
}
v___jp_4772_:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; 
lean_inc_ref(v___y_4774_);
v___x_4778_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___y_4775_, v___y_4774_, v_body_4770_, v___y_4777_);
v___x_4779_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_4776_, v___x_4778_, v___y_4773_);
return v___x_4779_;
}
v___jp_4780_:
{
lean_object* v_doc_4783_; 
v_doc_4783_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___y_4782_);
if (v_sticky_4771_ == 0)
{
lean_dec_ref(v_body_4770_);
lean_dec_ref(v_separationTk_4769_);
lean_dec_ref(v_signature_4768_);
return v_doc_4783_;
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v_lhs_4795_; lean_object* v___x_4796_; 
v___x_4784_ = l_Lean_Fmt_TaggedDoc_flattened(v_signature_4768_);
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
v___x_4786_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4787_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4785_, v___x_4786_);
v___x_4788_ = lean_box(0);
v___x_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4789_, 0, v_separationTk_4769_);
v___x_4790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4788_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
lean_ctor_set(v___x_4790_, 2, v___x_4788_);
v___x_4791_ = lean_unsigned_to_nat(2u);
v___x_4792_ = lean_mk_empty_array_with_capacity(v___x_4791_);
v___x_4793_ = lean_array_push(v___x_4792_, v___x_4787_);
v___x_4794_ = lean_array_push(v___x_4793_, v___x_4790_);
v_lhs_4795_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4794_);
lean_dec_ref(v___x_4794_);
lean_inc_ref(v_body_4770_);
v___x_4796_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_body_4770_);
if (lean_obj_tag(v___x_4796_) == 1)
{
lean_object* v_val_4797_; uint8_t v_kind_4798_; lean_object* v___x_4799_; 
v_val_4797_ = lean_ctor_get(v___x_4796_, 0);
lean_inc(v_val_4797_);
lean_dec_ref_known(v___x_4796_, 1);
v_kind_4798_ = lean_ctor_get_uint8(v_val_4797_, sizeof(void*)*1);
lean_dec(v_val_4797_);
v___x_4799_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
if (v_kind_4798_ == 1)
{
uint8_t v___x_4800_; 
v___x_4800_ = 0;
v___y_4773_ = v_kind_4798_;
v___y_4774_ = v___x_4799_;
v___y_4775_ = v_lhs_4795_;
v___y_4776_ = v_doc_4783_;
v___y_4777_ = v___x_4800_;
goto v___jp_4772_;
}
else
{
v___y_4773_ = v_kind_4798_;
v___y_4774_ = v___x_4799_;
v___y_4775_ = v_lhs_4795_;
v___y_4776_ = v_doc_4783_;
v___y_4777_ = v_sticky_4771_;
goto v___jp_4772_;
}
}
else
{
lean_object* v___x_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___x_4804_; 
lean_dec(v___x_4796_);
v___x_4801_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4802_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4795_, v___x_4801_, v_body_4770_, v___y_4781_);
v___x_4803_ = 0;
v___x_4804_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4783_, v___x_4802_, v___x_4803_);
return v___x_4804_;
}
}
}
v___jp_4805_:
{
uint8_t v___x_4807_; 
v___x_4807_ = 1;
if (v___y_4806_ == 0)
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v_lhs_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
lean_inc_ref(v_signature_4768_);
v___x_4808_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4768_);
v___x_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4808_);
v___x_4810_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4811_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4809_, v___x_4810_);
v___x_4812_ = lean_box(0);
lean_inc_ref(v_separationTk_4769_);
v___x_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4813_, 0, v_separationTk_4769_);
v___x_4814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4812_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
lean_ctor_set(v___x_4814_, 2, v___x_4812_);
v___x_4815_ = lean_unsigned_to_nat(2u);
v___x_4816_ = lean_mk_empty_array_with_capacity(v___x_4815_);
v___x_4817_ = lean_array_push(v___x_4816_, v___x_4811_);
v___x_4818_ = lean_array_push(v___x_4817_, v___x_4814_);
v_lhs_4819_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4818_);
lean_dec_ref(v___x_4818_);
v___x_4820_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_body_4770_);
v___x_4821_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4819_, v___x_4820_, v_body_4770_, v___x_4807_);
v___y_4781_ = v___x_4807_;
v___y_4782_ = v___x_4821_;
goto v___jp_4780_;
}
else
{
lean_inc_ref(v_signature_4768_);
v___y_4781_ = v___x_4807_;
v___y_4782_ = v_signature_4768_;
goto v___jp_4780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object* v_signature_4824_, lean_object* v_separationTk_4825_, lean_object* v_body_4826_, lean_object* v_sticky_4827_){
_start:
{
uint8_t v_sticky_boxed_4828_; lean_object* v_res_4829_; 
v_sticky_boxed_4828_ = lean_unbox(v_sticky_4827_);
v_res_4829_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_4824_, v_separationTk_4825_, v_body_4826_, v_sticky_boxed_4828_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object* v_signature_4830_, lean_object* v_matchAlts_4831_){
_start:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4832_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4830_);
v___x_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4832_);
v___x_4834_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4835_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4833_, v___x_4834_);
v___x_4836_ = lean_box(0);
v___x_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4837_, 0, v_matchAlts_4831_);
v___x_4838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4836_);
lean_ctor_set(v___x_4838_, 1, v___x_4837_);
lean_ctor_set(v___x_4838_, 2, v___x_4836_);
v___x_4839_ = lean_unsigned_to_nat(2u);
v___x_4840_ = lean_mk_empty_array_with_capacity(v___x_4839_);
v___x_4841_ = lean_array_push(v___x_4840_, v___x_4835_);
v___x_4842_ = lean_array_push(v___x_4841_, v___x_4838_);
v___x_4843_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4842_);
lean_dec_ref(v___x_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object* v_signature_4844_, lean_object* v_whereTk_4845_, lean_object* v_body_4846_){
_start:
{
uint8_t v___x_4847_; 
v___x_4847_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4846_);
if (v___x_4847_ == 0)
{
uint8_t v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v_lhs_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; 
v___x_4848_ = 1;
v___x_4849_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4844_);
v___x_4850_ = lean_unsigned_to_nat(2u);
v___x_4851_ = lean_mk_empty_array_with_capacity(v___x_4850_);
v___x_4852_ = lean_array_push(v___x_4851_, v___x_4849_);
v___x_4853_ = lean_array_push(v___x_4852_, v_whereTk_4845_);
v_lhs_4854_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4853_);
lean_dec_ref(v___x_4853_);
v___x_4855_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4856_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4854_, v___x_4855_, v_body_4846_, v___x_4848_);
v___x_4857_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4856_);
return v___x_4857_;
}
else
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
lean_dec_ref(v_body_4846_);
v___x_4858_ = lean_unsigned_to_nat(2u);
v___x_4859_ = lean_mk_empty_array_with_capacity(v___x_4858_);
v___x_4860_ = lean_array_push(v___x_4859_, v_signature_4844_);
v___x_4861_ = lean_array_push(v___x_4860_, v_whereTk_4845_);
v___x_4862_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4861_);
lean_dec_ref(v___x_4861_);
return v___x_4862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object* v_lbs_4864_, lean_object* v_lhses_4865_, lean_object* v_subBinderGroups_4866_, lean_object* v_typeAscriptionTk_x3f_4867_, lean_object* v_type_x3f_4868_, lean_object* v_colonEqTk_x3f_4869_, lean_object* v_default_x3f_4870_, lean_object* v_rbs_4871_, lean_object* v_kind_4872_){
_start:
{
lean_object* v_lbs_4873_; lean_object* v___x_4874_; lean_object* v_binderSignature_4875_; uint8_t v___x_4876_; lean_object* v_simpleBinder_4877_; lean_object* v_rbs_4878_; lean_object* v___x_4879_; 
v_lbs_4873_ = l_Lean_Fmt_Layouts_atomic(v_lbs_4864_);
v___x_4874_ = ((lean_object*)(l_Lean_Fmt_Layouts_binder___closed__0));
v_binderSignature_4875_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lhses_4865_, v_subBinderGroups_4866_, v_typeAscriptionTk_x3f_4867_, v_type_x3f_4868_, v_kind_4872_, v___x_4874_);
v___x_4876_ = 0;
v_simpleBinder_4877_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_binderSignature_4875_, v_colonEqTk_x3f_4869_, v_default_x3f_4870_, v___x_4876_);
v_rbs_4878_ = l_Lean_Fmt_Layouts_atomic(v_rbs_4871_);
v___x_4879_ = l_Lean_Fmt_Layouts_parens(v_lbs_4873_, v_simpleBinder_4877_, v_rbs_4878_);
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object* v_lbs_4880_, lean_object* v_lhses_4881_, lean_object* v_subBinderGroups_4882_, lean_object* v_typeAscriptionTk_x3f_4883_, lean_object* v_type_x3f_4884_, lean_object* v_colonEqTk_x3f_4885_, lean_object* v_default_x3f_4886_, lean_object* v_rbs_4887_, lean_object* v_kind_4888_){
_start:
{
lean_object* v_res_4889_; 
v_res_4889_ = l_Lean_Fmt_Layouts_binder(v_lbs_4880_, v_lhses_4881_, v_subBinderGroups_4882_, v_typeAscriptionTk_x3f_4883_, v_type_x3f_4884_, v_colonEqTk_x3f_4885_, v_default_x3f_4886_, v_rbs_4887_, v_kind_4888_);
lean_dec(v_kind_4888_);
lean_dec_ref(v_rbs_4887_);
lean_dec_ref(v_subBinderGroups_4882_);
lean_dec_ref(v_lhses_4881_);
lean_dec_ref(v_lbs_4880_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object* v_keywordTk_4893_, lean_object* v_config_4894_, lean_object* v_decl_4895_, uint8_t v_format_4896_){
_start:
{
lean_object* v___f_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v_signature_4903_; lean_object* v___y_4905_; 
v___f_4897_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_4898_ = lean_unsigned_to_nat(2u);
v___x_4899_ = lean_mk_empty_array_with_capacity(v___x_4898_);
lean_inc_ref(v___x_4899_);
v___x_4900_ = lean_array_push(v___x_4899_, v_keywordTk_4893_);
v___x_4901_ = lean_array_push(v___x_4900_, v_config_4894_);
v___x_4902_ = ((lean_object*)(l_Lean_Fmt_Layouts_letDecl___closed__0));
v_signature_4903_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4901_, v___x_4902_);
if (v_format_4896_ == 0)
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_Fmt_TaggedDoc_space;
v___y_4905_ = v___x_4917_;
goto v___jp_4904_;
}
else
{
lean_object* v___x_4918_; 
v___x_4918_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4905_ = v___x_4918_;
goto v___jp_4904_;
}
v___jp_4904_:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4906_, 0, v_signature_4903_);
lean_inc_ref(v___y_4905_);
v___x_4907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4907_, 0, v___y_4905_);
lean_ctor_set(v___x_4907_, 1, v___f_4897_);
v___x_4908_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4906_, v___x_4907_);
v___x_4909_ = lean_box(0);
v___x_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4910_, 0, v_decl_4895_);
v___x_4911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4909_);
lean_ctor_set(v___x_4911_, 1, v___x_4910_);
lean_ctor_set(v___x_4911_, 2, v___x_4909_);
v___x_4912_ = lean_array_push(v___x_4899_, v___x_4908_);
v___x_4913_ = lean_array_push(v___x_4912_, v___x_4911_);
v___x_4914_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4913_);
lean_dec_ref(v___x_4913_);
v___x_4915_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4914_);
v___x_4916_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4915_);
return v___x_4916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object* v_keywordTk_4919_, lean_object* v_config_4920_, lean_object* v_decl_4921_, lean_object* v_format_4922_){
_start:
{
uint8_t v_format_boxed_4923_; lean_object* v_res_4924_; 
v_format_boxed_4923_ = lean_unbox(v_format_4922_);
v_res_4924_ = l_Lean_Fmt_Layouts_letDecl(v_keywordTk_4919_, v_config_4920_, v_decl_4921_, v_format_boxed_4923_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t v_sz_4925_, size_t v_i_4926_, lean_object* v_bs_4927_){
_start:
{
uint8_t v___x_4928_; 
v___x_4928_ = lean_usize_dec_lt(v_i_4926_, v_sz_4925_);
if (v___x_4928_ == 0)
{
return v_bs_4927_;
}
else
{
lean_object* v_v_4929_; lean_object* v_quantifier_4930_; lean_object* v_binderGroups_4931_; lean_object* v_typeAscriptionTk_x3f_4932_; lean_object* v_type_x3f_4933_; lean_object* v_separationTk_4934_; lean_object* v___x_4935_; lean_object* v_bs_x27_4936_; lean_object* v___x_4937_; lean_object* v_signature_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; uint8_t v___x_4944_; lean_object* v___x_4945_; size_t v___x_4946_; size_t v___x_4947_; lean_object* v___x_4948_; 
v_v_4929_ = lean_array_uget_borrowed(v_bs_4927_, v_i_4926_);
v_quantifier_4930_ = lean_ctor_get(v_v_4929_, 0);
lean_inc_ref(v_quantifier_4930_);
v_binderGroups_4931_ = lean_ctor_get(v_v_4929_, 1);
lean_inc_ref(v_binderGroups_4931_);
v_typeAscriptionTk_x3f_4932_ = lean_ctor_get(v_v_4929_, 2);
lean_inc_ref(v_typeAscriptionTk_x3f_4932_);
v_type_x3f_4933_ = lean_ctor_get(v_v_4929_, 3);
lean_inc_ref(v_type_x3f_4933_);
v_separationTk_4934_ = lean_ctor_get(v_v_4929_, 4);
lean_inc_ref(v_separationTk_4934_);
v___x_4935_ = lean_unsigned_to_nat(0u);
v_bs_x27_4936_ = lean_array_uset(v_bs_4927_, v_i_4926_, v___x_4935_);
v___x_4937_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v_signature_4938_ = l_Lean_Fmt_Layouts_localSignature(v___x_4937_, v_binderGroups_4931_, v_typeAscriptionTk_x3f_4932_, v_type_x3f_4933_);
lean_dec_ref(v_binderGroups_4931_);
v___x_4939_ = lean_unsigned_to_nat(2u);
v___x_4940_ = lean_mk_empty_array_with_capacity(v___x_4939_);
v___x_4941_ = lean_array_push(v___x_4940_, v_signature_4938_);
v___x_4942_ = lean_array_push(v___x_4941_, v_separationTk_4934_);
v___x_4943_ = l_Lean_Fmt_Layouts_atomic(v___x_4942_);
lean_dec_ref(v___x_4942_);
v___x_4944_ = 2;
v___x_4945_ = l_Lean_Fmt_Layouts_prefixOperator(v_quantifier_4930_, v___x_4943_, v___x_4944_);
v___x_4946_ = ((size_t)1ULL);
v___x_4947_ = lean_usize_add(v_i_4926_, v___x_4946_);
v___x_4948_ = lean_array_uset(v_bs_x27_4936_, v_i_4926_, v___x_4945_);
v_i_4926_ = v___x_4947_;
v_bs_4927_ = v___x_4948_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object* v_sz_4950_, lean_object* v_i_4951_, lean_object* v_bs_4952_){
_start:
{
size_t v_sz_boxed_4953_; size_t v_i_boxed_4954_; lean_object* v_res_4955_; 
v_sz_boxed_4953_ = lean_unbox_usize(v_sz_4950_);
lean_dec(v_sz_4950_);
v_i_boxed_4954_ = lean_unbox_usize(v_i_4951_);
lean_dec(v_i_4951_);
v_res_4955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_boxed_4953_, v_i_boxed_4954_, v_bs_4952_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t v_sz_4956_, size_t v_i_4957_, lean_object* v_bs_4958_){
_start:
{
uint8_t v___x_4959_; 
v___x_4959_ = lean_usize_dec_lt(v_i_4957_, v_sz_4956_);
if (v___x_4959_ == 0)
{
return v_bs_4958_;
}
else
{
lean_object* v_v_4960_; lean_object* v___x_4961_; lean_object* v_bs_x27_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; size_t v___x_4965_; size_t v___x_4966_; lean_object* v___x_4967_; 
v_v_4960_ = lean_array_uget(v_bs_4958_, v_i_4957_);
v___x_4961_ = lean_unsigned_to_nat(0u);
v_bs_x27_4962_ = lean_array_uset(v_bs_4958_, v_i_4957_, v___x_4961_);
v___x_4963_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4960_);
v___x_4964_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4964_, 0, v___x_4963_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*1, v___x_4959_);
v___x_4965_ = ((size_t)1ULL);
v___x_4966_ = lean_usize_add(v_i_4957_, v___x_4965_);
v___x_4967_ = lean_array_uset(v_bs_x27_4962_, v_i_4957_, v___x_4964_);
v_i_4957_ = v___x_4966_;
v_bs_4958_ = v___x_4967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object* v_sz_4969_, lean_object* v_i_4970_, lean_object* v_bs_4971_){
_start:
{
size_t v_sz_boxed_4972_; size_t v_i_boxed_4973_; lean_object* v_res_4974_; 
v_sz_boxed_4972_ = lean_unbox_usize(v_sz_4969_);
lean_dec(v_sz_4969_);
v_i_boxed_4973_ = lean_unbox_usize(v_i_4970_);
lean_dec(v_i_4970_);
v_res_4974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_boxed_4972_, v_i_boxed_4973_, v_bs_4971_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object* v_quantifierHeads_4975_, lean_object* v_body_4976_){
_start:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; uint8_t v___x_4979_; 
v___x_4977_ = lean_array_get_size(v_quantifierHeads_4975_);
v___x_4978_ = lean_unsigned_to_nat(0u);
v___x_4979_ = lean_nat_dec_eq(v___x_4977_, v___x_4978_);
if (v___x_4979_ == 0)
{
size_t v_sz_4980_; size_t v___x_4981_; lean_object* v_quantifierHeads_4982_; size_t v_sz_4983_; lean_object* v_quantifierHeads_4984_; lean_object* v___x_4985_; lean_object* v_components_4986_; lean_object* v___x_4987_; lean_object* v_quantifiers_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; 
v_sz_4980_ = lean_array_size(v_quantifierHeads_4975_);
v___x_4981_ = ((size_t)0ULL);
v_quantifierHeads_4982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_4980_, v___x_4981_, v_quantifierHeads_4975_);
v_sz_4983_ = lean_array_size(v_quantifierHeads_4982_);
v_quantifierHeads_4984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_4983_, v___x_4981_, v_quantifierHeads_4982_);
v___x_4985_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4985_, 0, v_body_4976_);
lean_ctor_set_uint8(v___x_4985_, sizeof(void*)*1, v___x_4979_);
v_components_4986_ = lean_array_push(v_quantifierHeads_4984_, v___x_4985_);
v___x_4987_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_quantifiers_4988_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(v_components_4986_, v___x_4987_);
v___x_4989_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_quantifiers_4988_);
v___x_4990_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4989_);
return v___x_4990_;
}
else
{
lean_dec_ref(v_quantifierHeads_4975_);
return v_body_4976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object* v_lbTk_4994_, lean_object* v_lhs_4995_, lean_object* v_sepTk_4996_, lean_object* v_rhs_4997_, lean_object* v_rbTk_4998_, lean_object* v_format_4999_){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v_body_5007_; lean_object* v___x_5008_; 
v___x_5000_ = lean_unsigned_to_nat(3u);
v___x_5001_ = lean_mk_empty_array_with_capacity(v___x_5000_);
v___x_5002_ = lean_array_push(v___x_5001_, v_lhs_4995_);
v___x_5003_ = lean_array_push(v___x_5002_, v_sepTk_4996_);
v___x_5004_ = lean_array_push(v___x_5003_, v_rhs_4997_);
v___x_5005_ = ((lean_object*)(l_Lean_Fmt_Layouts_subtype___closed__0));
v___x_5006_ = l_Lean_Fmt_Layouts_infixOperator(v___x_5004_, v___x_5005_);
v_body_5007_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_5006_);
v___x_5008_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_4994_, v_body_5007_, v_rbTk_4998_, v_format_4999_);
return v___x_5008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object* v_tk_5009_, lean_object* v_block_5010_, uint8_t v_allowFlattening_5011_){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5012_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_5013_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tk_5009_, v___x_5012_, v_block_5010_, v_allowFlattening_5011_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object* v_tk_5014_, lean_object* v_block_5015_, lean_object* v_allowFlattening_5016_){
_start:
{
uint8_t v_allowFlattening_boxed_5017_; lean_object* v_res_5018_; 
v_allowFlattening_boxed_5017_ = lean_unbox(v_allowFlattening_5016_);
v_res_5018_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_tk_5014_, v_block_5015_, v_allowFlattening_boxed_5017_);
return v_res_5018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t v_allowFlattening_5019_, size_t v_sz_5020_, size_t v_i_5021_, lean_object* v_bs_5022_){
_start:
{
uint8_t v___x_5023_; 
v___x_5023_ = lean_usize_dec_lt(v_i_5021_, v_sz_5020_);
if (v___x_5023_ == 0)
{
return v_bs_5022_;
}
else
{
lean_object* v_v_5024_; lean_object* v_elseTk_5025_; lean_object* v_ifTk_5026_; lean_object* v_cond_5027_; lean_object* v_thenTk_5028_; lean_object* v_thenBlock_5029_; lean_object* v___x_5030_; lean_object* v_bs_x27_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v_tk_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; lean_object* v___x_5040_; lean_object* v_head_5041_; lean_object* v_then_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v_trailingThen_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v_leadingThen_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; size_t v___x_5062_; size_t v___x_5063_; lean_object* v___x_5064_; 
v_v_5024_ = lean_array_uget_borrowed(v_bs_5022_, v_i_5021_);
v_elseTk_5025_ = lean_ctor_get(v_v_5024_, 0);
lean_inc_ref(v_elseTk_5025_);
v_ifTk_5026_ = lean_ctor_get(v_v_5024_, 1);
lean_inc_ref(v_ifTk_5026_);
v_cond_5027_ = lean_ctor_get(v_v_5024_, 2);
lean_inc_ref(v_cond_5027_);
v_thenTk_5028_ = lean_ctor_get(v_v_5024_, 3);
lean_inc_ref(v_thenTk_5028_);
v_thenBlock_5029_ = lean_ctor_get(v_v_5024_, 4);
lean_inc_ref(v_thenBlock_5029_);
v___x_5030_ = lean_unsigned_to_nat(0u);
v_bs_x27_5031_ = lean_array_uset(v_bs_5022_, v_i_5021_, v___x_5030_);
v___x_5032_ = lean_unsigned_to_nat(2u);
v___x_5033_ = lean_mk_empty_array_with_capacity(v___x_5032_);
lean_inc_ref_n(v___x_5033_, 4);
v___x_5034_ = lean_array_push(v___x_5033_, v_elseTk_5025_);
v___x_5035_ = lean_array_push(v___x_5034_, v_ifTk_5026_);
v_tk_5036_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_5035_);
lean_dec_ref(v___x_5035_);
v___x_5037_ = lean_array_push(v___x_5033_, v_tk_5036_);
v___x_5038_ = lean_array_push(v___x_5037_, v_cond_5027_);
v___x_5039_ = 0;
v___x_5040_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_5040_, 0, v___x_5023_);
lean_ctor_set_uint8(v___x_5040_, 1, v___x_5039_);
lean_ctor_set_uint8(v___x_5040_, 2, v___x_5039_);
lean_ctor_set_uint8(v___x_5040_, 3, v___x_5039_);
v_head_5041_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_5038_, v___x_5040_);
v_then_5042_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_thenTk_5028_, v_thenBlock_5029_, v_allowFlattening_5019_);
lean_inc_ref(v_head_5041_);
v___x_5043_ = l_Lean_Fmt_TaggedDoc_flattened(v_head_5041_);
v___x_5044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5043_);
v___x_5045_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_5046_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_5044_, v___x_5045_);
v___x_5047_ = lean_box(0);
v___x_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5048_, 0, v_then_5042_);
v___x_5049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5047_);
lean_ctor_set(v___x_5049_, 1, v___x_5048_);
lean_ctor_set(v___x_5049_, 2, v___x_5047_);
v___x_5050_ = lean_array_push(v___x_5033_, v___x_5046_);
lean_inc_ref(v___x_5049_);
v___x_5051_ = lean_array_push(v___x_5050_, v___x_5049_);
v_trailingThen_5052_ = l_Lean_Fmt_TaggedDoc_combine(v___x_5051_);
lean_dec_ref(v___x_5051_);
v___x_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5053_, 0, v_head_5041_);
v___x_5054_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_5055_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_5053_, v___x_5054_);
v___x_5056_ = lean_array_push(v___x_5033_, v___x_5055_);
v___x_5057_ = lean_array_push(v___x_5056_, v___x_5049_);
v_leadingThen_5058_ = l_Lean_Fmt_TaggedDoc_combine(v___x_5057_);
lean_dec_ref(v___x_5057_);
v___x_5059_ = lean_array_push(v___x_5033_, v_trailingThen_5052_);
v___x_5060_ = lean_array_push(v___x_5059_, v_leadingThen_5058_);
v___x_5061_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_5060_);
v___x_5062_ = ((size_t)1ULL);
v___x_5063_ = lean_usize_add(v_i_5021_, v___x_5062_);
v___x_5064_ = lean_array_uset(v_bs_x27_5031_, v_i_5021_, v___x_5061_);
v_i_5021_ = v___x_5063_;
v_bs_5022_ = v___x_5064_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object* v_allowFlattening_5066_, lean_object* v_sz_5067_, lean_object* v_i_5068_, lean_object* v_bs_5069_){
_start:
{
uint8_t v_allowFlattening_boxed_5070_; size_t v_sz_boxed_5071_; size_t v_i_boxed_5072_; lean_object* v_res_5073_; 
v_allowFlattening_boxed_5070_ = lean_unbox(v_allowFlattening_5066_);
v_sz_boxed_5071_ = lean_unbox_usize(v_sz_5067_);
lean_dec(v_sz_5067_);
v_i_boxed_5072_ = lean_unbox_usize(v_i_5068_);
lean_dec(v_i_5068_);
v_res_5073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_boxed_5070_, v_sz_boxed_5071_, v_i_boxed_5072_, v_bs_5069_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object* v_elseIfs_5074_, lean_object* v_elseTk_5075_, lean_object* v_elseBlock_5076_, uint8_t v_allowFlattening_5077_){
_start:
{
size_t v_sz_5078_; size_t v___x_5079_; lean_object* v_elseIfs_5080_; lean_object* v_else_5081_; lean_object* v_blocks_5082_; size_t v_sz_5083_; lean_object* v_blocks_5084_; lean_object* v_conditional_5085_; lean_object* v___x_5086_; 
v_sz_5078_ = lean_array_size(v_elseIfs_5074_);
v___x_5079_ = ((size_t)0ULL);
v_elseIfs_5080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_5077_, v_sz_5078_, v___x_5079_, v_elseIfs_5074_);
v_else_5081_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_elseTk_5075_, v_elseBlock_5076_, v_allowFlattening_5077_);
v_blocks_5082_ = lean_array_push(v_elseIfs_5080_, v_else_5081_);
v_sz_5083_ = lean_array_size(v_blocks_5082_);
v_blocks_5084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_5083_, v___x_5079_, v_blocks_5082_);
v_conditional_5085_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_5084_);
lean_dec_ref(v_blocks_5084_);
v___x_5086_ = l_Lean_Fmt_TaggedDoc_aligned(v_conditional_5085_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object* v_elseIfs_5087_, lean_object* v_elseTk_5088_, lean_object* v_elseBlock_5089_, lean_object* v_allowFlattening_5090_){
_start:
{
uint8_t v_allowFlattening_boxed_5091_; lean_object* v_res_5092_; 
v_allowFlattening_boxed_5091_ = lean_unbox(v_allowFlattening_5090_);
v_res_5092_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5087_, v_elseTk_5088_, v_elseBlock_5089_, v_allowFlattening_boxed_5091_);
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object* v_as_5093_, size_t v_i_5094_, size_t v_stop_5095_, lean_object* v_b_5096_){
_start:
{
lean_object* v___y_5098_; uint8_t v___x_5102_; 
v___x_5102_ = lean_usize_dec_eq(v_i_5094_, v_stop_5095_);
if (v___x_5102_ == 0)
{
lean_object* v___x_5103_; uint8_t v___y_5105_; lean_object* v_elseTk_5116_; lean_object* v_ifTk_5117_; uint8_t v___x_5118_; 
v___x_5103_ = lean_array_uget_borrowed(v_as_5093_, v_i_5094_);
v_elseTk_5116_ = lean_ctor_get(v___x_5103_, 0);
v_ifTk_5117_ = lean_ctor_get(v___x_5103_, 1);
v___x_5118_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_elseTk_5116_);
if (v___x_5118_ == 0)
{
v___y_5105_ = v___x_5118_;
goto v___jp_5104_;
}
else
{
uint8_t v___x_5119_; 
v___x_5119_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_ifTk_5117_);
v___y_5105_ = v___x_5119_;
goto v___jp_5104_;
}
v___jp_5104_:
{
if (v___y_5105_ == 0)
{
lean_object* v___x_5106_; 
lean_inc(v___x_5103_);
v___x_5106_ = lean_array_push(v_b_5096_, v___x_5103_);
v___y_5098_ = v___x_5106_;
goto v___jp_5097_;
}
else
{
lean_object* v_cond_5107_; lean_object* v_thenTk_5108_; lean_object* v_thenBlock_5109_; uint8_t v___x_5110_; 
v_cond_5107_ = lean_ctor_get(v___x_5103_, 2);
v_thenTk_5108_ = lean_ctor_get(v___x_5103_, 3);
v_thenBlock_5109_ = lean_ctor_get(v___x_5103_, 4);
v___x_5110_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_cond_5107_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; 
lean_inc(v___x_5103_);
v___x_5111_ = lean_array_push(v_b_5096_, v___x_5103_);
v___y_5098_ = v___x_5111_;
goto v___jp_5097_;
}
else
{
uint8_t v___x_5112_; 
v___x_5112_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenTk_5108_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5113_; 
lean_inc(v___x_5103_);
v___x_5113_ = lean_array_push(v_b_5096_, v___x_5103_);
v___y_5098_ = v___x_5113_;
goto v___jp_5097_;
}
else
{
uint8_t v___x_5114_; 
v___x_5114_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenBlock_5109_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; 
lean_inc(v___x_5103_);
v___x_5115_ = lean_array_push(v_b_5096_, v___x_5103_);
v___y_5098_ = v___x_5115_;
goto v___jp_5097_;
}
else
{
v___y_5098_ = v_b_5096_;
goto v___jp_5097_;
}
}
}
}
}
}
else
{
return v_b_5096_;
}
v___jp_5097_:
{
size_t v___x_5099_; size_t v___x_5100_; 
v___x_5099_ = ((size_t)1ULL);
v___x_5100_ = lean_usize_add(v_i_5094_, v___x_5099_);
v_i_5094_ = v___x_5100_;
v_b_5096_ = v___y_5098_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object* v_as_5120_, lean_object* v_i_5121_, lean_object* v_stop_5122_, lean_object* v_b_5123_){
_start:
{
size_t v_i_boxed_5124_; size_t v_stop_boxed_5125_; lean_object* v_res_5126_; 
v_i_boxed_5124_ = lean_unbox_usize(v_i_5121_);
lean_dec(v_i_5121_);
v_stop_boxed_5125_ = lean_unbox_usize(v_stop_5122_);
lean_dec(v_stop_5122_);
v_res_5126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_as_5120_, v_i_boxed_5124_, v_stop_boxed_5125_, v_b_5123_);
lean_dec_ref(v_as_5120_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object* v_ifTk_5129_, lean_object* v_cond_5130_, lean_object* v_thenTk_5131_, lean_object* v_thenBlock_5132_, lean_object* v_elseIfs_5133_, lean_object* v_elseTk_5134_, lean_object* v_elseBlock_5135_, uint8_t v_allowFlattening_5136_){
_start:
{
lean_object* v___y_5138_; uint8_t v___y_5139_; lean_object* v___y_5158_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5162_ = lean_unsigned_to_nat(0u);
v___x_5163_ = lean_array_get_size(v_elseIfs_5133_);
v___x_5164_ = ((lean_object*)(l_Lean_Fmt_Layouts_conditional___closed__0));
v___x_5165_ = lean_nat_dec_lt(v___x_5162_, v___x_5163_);
if (v___x_5165_ == 0)
{
v___y_5158_ = v___x_5164_;
goto v___jp_5157_;
}
else
{
uint8_t v___x_5166_; 
v___x_5166_ = lean_nat_dec_le(v___x_5163_, v___x_5163_);
if (v___x_5166_ == 0)
{
if (v___x_5165_ == 0)
{
v___y_5158_ = v___x_5164_;
goto v___jp_5157_;
}
else
{
size_t v___x_5167_; size_t v___x_5168_; lean_object* v___x_5169_; 
v___x_5167_ = ((size_t)0ULL);
v___x_5168_ = lean_usize_of_nat(v___x_5163_);
v___x_5169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_5133_, v___x_5167_, v___x_5168_, v___x_5164_);
v___y_5158_ = v___x_5169_;
goto v___jp_5157_;
}
}
else
{
size_t v___x_5170_; size_t v___x_5171_; lean_object* v___x_5172_; 
v___x_5170_ = ((size_t)0ULL);
v___x_5171_ = lean_usize_of_nat(v___x_5163_);
v___x_5172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_5133_, v___x_5170_, v___x_5171_, v___x_5164_);
v___y_5158_ = v___x_5172_;
goto v___jp_5157_;
}
}
v___jp_5137_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v_elseIfs_5145_; 
v___x_5140_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5140_);
lean_ctor_set(v___x_5141_, 1, v_ifTk_5129_);
lean_ctor_set(v___x_5141_, 2, v_cond_5130_);
lean_ctor_set(v___x_5141_, 3, v_thenTk_5131_);
lean_ctor_set(v___x_5141_, 4, v_thenBlock_5132_);
v___x_5142_ = lean_unsigned_to_nat(1u);
v___x_5143_ = lean_mk_empty_array_with_capacity(v___x_5142_);
v___x_5144_ = lean_array_push(v___x_5143_, v___x_5141_);
v_elseIfs_5145_ = l_Array_append___redArg(v___x_5144_, v___y_5138_);
lean_dec_ref(v___y_5138_);
if (v___y_5139_ == 0)
{
lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5146_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5145_, v_elseTk_5134_, v_elseBlock_5135_, v___y_5139_);
v___x_5147_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_5146_);
return v___x_5147_;
}
else
{
lean_object* v___x_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
lean_inc_ref(v_elseBlock_5135_);
lean_inc_ref(v_elseTk_5134_);
lean_inc_ref(v_elseIfs_5145_);
v___x_5148_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5145_, v_elseTk_5134_, v_elseBlock_5135_, v___y_5139_);
v___x_5149_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_5148_);
v___x_5150_ = 0;
v___x_5151_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5145_, v_elseTk_5134_, v_elseBlock_5135_, v___x_5150_);
v___x_5152_ = lean_unsigned_to_nat(2u);
v___x_5153_ = lean_mk_empty_array_with_capacity(v___x_5152_);
v___x_5154_ = lean_array_push(v___x_5153_, v___x_5149_);
v___x_5155_ = lean_array_push(v___x_5154_, v___x_5151_);
v___x_5156_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_5155_);
return v___x_5156_;
}
}
v___jp_5157_:
{
if (v_allowFlattening_5136_ == 0)
{
v___y_5138_ = v___y_5158_;
v___y_5139_ = v_allowFlattening_5136_;
goto v___jp_5137_;
}
else
{
lean_object* v___x_5159_; lean_object* v___x_5160_; uint8_t v___x_5161_; 
v___x_5159_ = lean_array_get_size(v___y_5158_);
v___x_5160_ = lean_unsigned_to_nat(0u);
v___x_5161_ = lean_nat_dec_eq(v___x_5159_, v___x_5160_);
v___y_5138_ = v___y_5158_;
v___y_5139_ = v___x_5161_;
goto v___jp_5137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object* v_ifTk_5173_, lean_object* v_cond_5174_, lean_object* v_thenTk_5175_, lean_object* v_thenBlock_5176_, lean_object* v_elseIfs_5177_, lean_object* v_elseTk_5178_, lean_object* v_elseBlock_5179_, lean_object* v_allowFlattening_5180_){
_start:
{
uint8_t v_allowFlattening_boxed_5181_; lean_object* v_res_5182_; 
v_allowFlattening_boxed_5181_ = lean_unbox(v_allowFlattening_5180_);
v_res_5182_ = l_Lean_Fmt_Layouts_conditional(v_ifTk_5173_, v_cond_5174_, v_thenTk_5175_, v_thenBlock_5176_, v_elseIfs_5177_, v_elseTk_5178_, v_elseBlock_5179_, v_allowFlattening_boxed_5181_);
lean_dec_ref(v_elseIfs_5177_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object* v_prefix_5183_, lean_object* v_str_5184_){
_start:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; uint8_t v___x_5190_; lean_object* v___x_5191_; 
v___x_5185_ = lean_unsigned_to_nat(2u);
v___x_5186_ = lean_mk_empty_array_with_capacity(v___x_5185_);
v___x_5187_ = lean_array_push(v___x_5186_, v_prefix_5183_);
v___x_5188_ = lean_array_push(v___x_5187_, v_str_5184_);
v___x_5189_ = l_Lean_Fmt_Layouts_atomic(v___x_5188_);
lean_dec_ref(v___x_5188_);
v___x_5190_ = 0;
v___x_5191_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_5189_, v___x_5190_);
return v___x_5191_;
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

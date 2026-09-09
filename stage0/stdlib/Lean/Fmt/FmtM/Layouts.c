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
lean_object* l_Lean_Fmt_TaggedDoc_unindented(lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_hardNested(lean_object*);
lean_object* l_Lean_Fmt_TaggedDoc_stickyCombine(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_TaggedDoc_withPosition(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_nbuckets_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1562_ = lean_array_get_size(v_data_1561_);
v___x_1563_ = lean_unsigned_to_nat(2u);
v_nbuckets_1564_ = lean_nat_mul(v___x_1562_, v___x_1563_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_mk_array(v_nbuckets_1564_, v___x_1566_);
v___x_1568_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v___x_1565_, v_data_1561_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(lean_object* v_a_1569_, lean_object* v_x_1570_){
_start:
{
if (lean_obj_tag(v_x_1570_) == 0)
{
uint8_t v___x_1571_; 
v___x_1571_ = 0;
return v___x_1571_;
}
else
{
lean_object* v_key_1572_; lean_object* v_tail_1573_; size_t v_ptr_1574_; size_t v_ptr_1575_; uint8_t v___x_1576_; 
v_key_1572_ = lean_ctor_get(v_x_1570_, 0);
v_tail_1573_ = lean_ctor_get(v_x_1570_, 2);
v_ptr_1574_ = lean_ctor_get_usize(v_key_1572_, 1);
v_ptr_1575_ = lean_ctor_get_usize(v_a_1569_, 1);
v___x_1576_ = lean_usize_dec_eq(v_ptr_1574_, v_ptr_1575_);
if (v___x_1576_ == 0)
{
v_x_1570_ = v_tail_1573_;
goto _start;
}
else
{
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg___boxed(lean_object* v_a_1578_, lean_object* v_x_1579_){
_start:
{
uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_res_1580_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1578_, v_x_1579_);
lean_dec(v_x_1579_);
lean_dec_ref(v_a_1578_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(lean_object* v_m_1582_, lean_object* v_a_1583_, lean_object* v_b_1584_){
_start:
{
lean_object* v_size_1585_; lean_object* v_buckets_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1630_; 
v_size_1585_ = lean_ctor_get(v_m_1582_, 0);
v_buckets_1586_ = lean_ctor_get(v_m_1582_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_m_1582_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1588_ = v_m_1582_;
v_isShared_1589_ = v_isSharedCheck_1630_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_buckets_1586_);
lean_inc(v_size_1585_);
lean_dec(v_m_1582_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1630_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
size_t v_ptr_1590_; lean_object* v___x_1591_; uint64_t v___x_1592_; uint64_t v___x_1593_; uint64_t v___x_1594_; uint64_t v_fold_1595_; uint64_t v___x_1596_; uint64_t v___x_1597_; uint64_t v___x_1598_; size_t v___x_1599_; size_t v___x_1600_; size_t v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; lean_object* v_bkt_1604_; uint8_t v___x_1605_; 
v_ptr_1590_ = lean_ctor_get_usize(v_a_1583_, 1);
v___x_1591_ = lean_array_get_size(v_buckets_1586_);
v___x_1592_ = lean_usize_to_uint64(v_ptr_1590_);
v___x_1593_ = 32ULL;
v___x_1594_ = lean_uint64_shift_right(v___x_1592_, v___x_1593_);
v_fold_1595_ = lean_uint64_xor(v___x_1592_, v___x_1594_);
v___x_1596_ = 16ULL;
v___x_1597_ = lean_uint64_shift_right(v_fold_1595_, v___x_1596_);
v___x_1598_ = lean_uint64_xor(v_fold_1595_, v___x_1597_);
v___x_1599_ = lean_uint64_to_usize(v___x_1598_);
v___x_1600_ = lean_usize_of_nat(v___x_1591_);
v___x_1601_ = ((size_t)1ULL);
v___x_1602_ = lean_usize_sub(v___x_1600_, v___x_1601_);
v___x_1603_ = lean_usize_land(v___x_1599_, v___x_1602_);
v_bkt_1604_ = lean_array_uget_borrowed(v_buckets_1586_, v___x_1603_);
v___x_1605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1583_, v_bkt_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v_size_x27_1607_; lean_object* v___x_1608_; lean_object* v_buckets_x27_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1606_ = lean_unsigned_to_nat(1u);
v_size_x27_1607_ = lean_nat_add(v_size_1585_, v___x_1606_);
lean_dec(v_size_1585_);
lean_inc(v_bkt_1604_);
v___x_1608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1583_);
lean_ctor_set(v___x_1608_, 1, v_b_1584_);
lean_ctor_set(v___x_1608_, 2, v_bkt_1604_);
v_buckets_x27_1609_ = lean_array_uset(v_buckets_1586_, v___x_1603_, v___x_1608_);
v___x_1610_ = lean_unsigned_to_nat(4u);
v___x_1611_ = lean_nat_mul(v_size_x27_1607_, v___x_1610_);
v___x_1612_ = lean_unsigned_to_nat(3u);
v___x_1613_ = lean_nat_div(v___x_1611_, v___x_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_array_get_size(v_buckets_x27_1609_);
v___x_1615_ = lean_nat_dec_le(v___x_1613_, v___x_1614_);
lean_dec(v___x_1613_);
if (v___x_1615_ == 0)
{
lean_object* v_val_1616_; lean_object* v___x_1618_; 
v_val_1616_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_buckets_x27_1609_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v_val_1616_);
lean_ctor_set(v___x_1588_, 0, v_size_x27_1607_);
v___x_1618_ = v___x_1588_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_size_x27_1607_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_val_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
else
{
lean_object* v___x_1621_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v_buckets_x27_1609_);
lean_ctor_set(v___x_1588_, 0, v_size_x27_1607_);
v___x_1621_ = v___x_1588_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_size_x27_1607_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_buckets_x27_1609_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_object* v___x_1623_; lean_object* v_buckets_x27_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_inc(v_bkt_1604_);
v___x_1623_ = lean_box(0);
v_buckets_x27_1624_ = lean_array_uset(v_buckets_1586_, v___x_1603_, v___x_1623_);
v___x_1625_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1583_, v_b_1584_, v_bkt_1604_);
v___x_1626_ = lean_array_uset(v_buckets_x27_1624_, v___x_1603_, v___x_1625_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___x_1626_);
v___x_1628_ = v___x_1588_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_size_1585_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___y_1634_; 
switch(lean_obj_tag(v_a_1631_))
{
case 1:
{
lean_dec_ref_known(v_a_1631_, 3);
v___y_1634_ = v_a_1632_;
goto v___jp_1633_;
}
case 2:
{
lean_dec_ref_known(v_a_1631_, 3);
v___y_1634_ = v_a_1632_;
goto v___jp_1633_;
}
case 3:
{
lean_object* v_d_1638_; lean_object* v___x_1639_; 
v_d_1638_ = lean_ctor_get(v_a_1631_, 3);
lean_inc(v_d_1638_);
lean_dec_ref_known(v_a_1631_, 4);
v___x_1639_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1638_, v_a_1632_);
return v___x_1639_;
}
case 4:
{
lean_object* v_d_1640_; lean_object* v___x_1641_; 
v_d_1640_ = lean_ctor_get(v_a_1631_, 2);
lean_inc(v_d_1640_);
lean_dec_ref_known(v_a_1631_, 3);
v___x_1641_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1640_, v_a_1632_);
return v___x_1641_;
}
case 5:
{
lean_object* v_d_1642_; lean_object* v___x_1643_; 
v_d_1642_ = lean_ctor_get(v_a_1631_, 2);
lean_inc(v_d_1642_);
lean_dec_ref_known(v_a_1631_, 3);
v___x_1643_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1642_, v_a_1632_);
return v___x_1643_;
}
case 6:
{
lean_object* v_d_1644_; lean_object* v___x_1645_; 
v_d_1644_ = lean_ctor_get(v_a_1631_, 3);
lean_inc(v_d_1644_);
lean_dec_ref_known(v_a_1631_, 4);
v___x_1645_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1644_, v_a_1632_);
return v___x_1645_;
}
case 7:
{
uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref_known(v_a_1631_, 3);
v___x_1646_ = 1;
v___x_1647_ = lean_box(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_a_1632_);
return v___x_1648_;
}
case 8:
{
lean_object* v_d_1649_; lean_object* v___x_1650_; 
v_d_1649_ = lean_ctor_get(v_a_1631_, 2);
lean_inc(v_d_1649_);
lean_dec_ref_known(v_a_1631_, 3);
v___x_1650_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1649_, v_a_1632_);
return v___x_1650_;
}
case 9:
{
lean_object* v_d_1651_; lean_object* v___x_1652_; 
v_d_1651_ = lean_ctor_get(v_a_1631_, 2);
lean_inc(v_d_1651_);
lean_dec_ref_known(v_a_1631_, 3);
v___x_1652_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1651_, v_a_1632_);
return v___x_1652_;
}
case 10:
{
lean_object* v_d_1653_; lean_object* v___x_1654_; 
v_d_1653_ = lean_ctor_get(v_a_1631_, 2);
lean_inc(v_d_1653_);
lean_dec_ref_known(v_a_1631_, 3);
v___x_1654_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1653_, v_a_1632_);
return v___x_1654_;
}
case 11:
{
lean_object* v_d_1655_; lean_object* v___x_1656_; 
v_d_1655_ = lean_ctor_get(v_a_1631_, 2);
lean_inc(v_d_1655_);
lean_dec_ref_known(v_a_1631_, 3);
v___x_1656_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1655_, v_a_1632_);
return v___x_1656_;
}
case 12:
{
lean_object* v_d_1657_; lean_object* v___x_1658_; 
v_d_1657_ = lean_ctor_get(v_a_1631_, 3);
lean_inc(v_d_1657_);
lean_dec_ref_known(v_a_1631_, 4);
v___x_1658_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1657_, v_a_1632_);
return v___x_1658_;
}
case 13:
{
lean_object* v_d_1659_; lean_object* v___x_1660_; 
v_d_1659_ = lean_ctor_get(v_a_1631_, 3);
lean_inc(v_d_1659_);
lean_dec_ref_known(v_a_1631_, 4);
v___x_1660_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_d_1659_, v_a_1632_);
return v___x_1660_;
}
case 14:
{
lean_object* v_a_1661_; lean_object* v_b_1662_; lean_object* v___x_1663_; lean_object* v_fst_1664_; lean_object* v_snd_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v_a_1661_ = lean_ctor_get(v_a_1631_, 2);
lean_inc(v_a_1661_);
v_b_1662_ = lean_ctor_get(v_a_1631_, 3);
lean_inc(v_b_1662_);
lean_dec_ref_known(v_a_1631_, 4);
v___x_1663_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_a_1661_, v_a_1632_);
v_fst_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_fst_1664_);
v_snd_1665_ = lean_ctor_get(v___x_1663_, 1);
lean_inc(v_snd_1665_);
lean_dec_ref(v___x_1663_);
v___x_1666_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_b_1662_, v_snd_1665_);
v___x_1667_ = lean_unbox(v_fst_1664_);
if (v___x_1667_ == 0)
{
lean_object* v_snd_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_snd_1668_ = lean_ctor_get(v___x_1666_, 1);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v___x_1666_, 0);
lean_dec(v_unused_1676_);
v___x_1670_ = v___x_1666_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_snd_1668_);
lean_dec(v___x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v_fst_1664_);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_fst_1664_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_snd_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_dec(v_fst_1664_);
return v___x_1666_;
}
}
default: 
{
uint8_t v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec(v_a_1631_);
v___x_1677_ = 0;
v___x_1678_ = lean_box(v___x_1677_);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1678_);
lean_ctor_set(v___x_1679_, 1, v_a_1632_);
return v___x_1679_;
}
}
v___jp_1633_:
{
uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = 0;
v___x_1636_ = lean_box(v___x_1635_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___y_1634_);
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(lean_object* v_v_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_cacheKey_1682_; lean_object* v___x_1683_; 
lean_inc(v_v_1680_);
v_cacheKey_1682_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_1680_);
v___x_1683_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_a_1681_, v_cacheKey_1682_);
if (lean_obj_tag(v___x_1683_) == 1)
{
lean_object* v_val_1684_; lean_object* v___x_1685_; 
lean_dec_ref(v_cacheKey_1682_);
lean_dec(v_v_1680_);
v_val_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_val_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v_val_1684_);
lean_ctor_set(v___x_1685_, 1, v_a_1681_);
return v___x_1685_;
}
else
{
lean_object* v___x_1686_; lean_object* v_fst_1687_; lean_object* v_snd_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v___x_1683_);
v___x_1686_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_v_1680_, v_a_1681_);
v_fst_1687_ = lean_ctor_get(v___x_1686_, 0);
v_snd_1688_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1690_ = v___x_1686_;
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_snd_1688_);
lean_inc(v_fst_1687_);
lean_dec(v___x_1686_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
lean_inc(v_fst_1687_);
v___x_1692_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_snd_1688_, v_cacheKey_1682_, v_fst_1687_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_fst_1687_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go(lean_object* v_00_u03c4_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_go___redArg(v_a_1698_, v_a_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized(lean_object* v_00_u03c4_1701_, lean_object* v_v_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1702_, v_a_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(lean_object* v_00_u03c4_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_m_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___redArg(v_m_1707_, v_a_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0___boxed(lean_object* v_00_u03c4_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_m_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0(v_00_u03c4_1710_, v_00_u03b2_1711_, v_m_1712_, v_a_1713_);
lean_dec_ref(v_a_1713_);
lean_dec_ref(v_m_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1(lean_object* v_00_u03c4_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_m_1717_, lean_object* v_a_1718_, lean_object* v_b_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1___redArg(v_m_1717_, v_a_1718_, v_b_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(lean_object* v_00_u03c4_1721_, lean_object* v_00_u03b2_1722_, lean_object* v_a_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___redArg(v_a_1723_, v_x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1___boxed(lean_object* v_00_u03c4_1726_, lean_object* v_00_u03b2_1727_, lean_object* v_a_1728_, lean_object* v_x_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__0_spec__1(v_00_u03c4_1726_, v_00_u03b2_1727_, v_a_1728_, v_x_1729_);
lean_dec(v_x_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(lean_object* v_00_u03c4_1731_, lean_object* v_00_u03b2_1732_, lean_object* v_a_1733_, lean_object* v_x_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___redArg(v_a_1733_, v_x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3___boxed(lean_object* v_00_u03c4_1736_, lean_object* v_00_u03b2_1737_, lean_object* v_a_1738_, lean_object* v_x_1739_){
_start:
{
uint8_t v_res_1740_; lean_object* v_r_1741_; 
v_res_1740_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__3(v_00_u03c4_1736_, v_00_u03b2_1737_, v_a_1738_, v_x_1739_);
lean_dec(v_x_1739_);
lean_dec_ref(v_a_1738_);
v_r_1741_ = lean_box(v_res_1740_);
return v_r_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4(lean_object* v_00_u03c4_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_data_1744_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4___redArg(v_data_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5(lean_object* v_00_u03c4_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_a_1748_, lean_object* v_b_1749_, lean_object* v_x_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__5___redArg(v_a_1748_, v_b_1749_, v_x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5(lean_object* v_00_u03c4_1752_, lean_object* v_00_u03b2_1753_, lean_object* v_i_1754_, lean_object* v_source_1755_, lean_object* v_target_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5___redArg(v_i_1754_, v_source_1755_, v_target_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03c4_1758_, lean_object* v_00_u03b2_1759_, lean_object* v_x_1760_, lean_object* v_x_1761_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized_spec__1_spec__4_spec__5_spec__6___redArg(v_x_1760_, v_x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = lean_box(0);
v___x_1764_ = lean_unsigned_to_nat(16u);
v___x_1765_ = lean_mk_array(v___x_1764_, v___x_1763_);
return v___x_1765_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__0);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___x_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(lean_object* v_v_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v_fst_1772_; 
v___x_1770_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg___closed__1);
v___x_1771_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1769_, v___x_1770_);
v_fst_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_fst_1772_);
lean_dec_ref(v___x_1771_);
return v_fst_1772_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(lean_object* v_00_u03c4_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_, lean_object* v_v_1776_){
_start:
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___redArg(v_v_1776_);
v___x_1778_ = lean_unbox(v___x_1777_);
lean_dec(v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___boxed(lean_object* v_00_u03c4_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_v_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned(v_00_u03c4_1779_, v_inst_1780_, v_inst_1781_, v_v_1782_);
lean_dec_ref(v_inst_1781_);
lean_dec_ref(v_inst_1780_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(uint8_t v_x_1785_){
_start:
{
switch(v_x_1785_)
{
case 0:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_unsigned_to_nat(0u);
return v___x_1786_;
}
case 1:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_unsigned_to_nat(1u);
return v___x_1787_;
}
default: 
{
lean_object* v___x_1788_; 
v___x_1788_ = lean_unsigned_to_nat(2u);
return v___x_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1789_){
_start:
{
uint8_t v_x_boxed_1790_; lean_object* v_res_1791_; 
v_x_boxed_1790_ = lean_unbox(v_x_1789_);
v_res_1791_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorIdx(v_x_boxed_1790_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(lean_object* v_k_1792_){
_start:
{
lean_inc(v_k_1792_);
return v_k_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___redArg(v_k_1793_);
lean_dec(v_k_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(lean_object* v_motive_1795_, lean_object* v_ctorIdx_1796_, uint8_t v_t_1797_, lean_object* v_h_1798_, lean_object* v_k_1799_){
_start:
{
lean_inc(v_k_1799_);
return v_k_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1800_, lean_object* v_ctorIdx_1801_, lean_object* v_t_1802_, lean_object* v_h_1803_, lean_object* v_k_1804_){
_start:
{
uint8_t v_t_boxed_1805_; lean_object* v_res_1806_; 
v_t_boxed_1805_ = lean_unbox(v_t_1802_);
v_res_1806_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_ctorElim(v_motive_1800_, v_ctorIdx_1801_, v_t_boxed_1805_, v_h_1803_, v_k_1804_);
lean_dec(v_k_1804_);
lean_dec(v_ctorIdx_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1807_){
_start:
{
lean_inc(v_withoutSpacing_1807_);
return v_withoutSpacing_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1808_);
lean_dec(v_withoutSpacing_1808_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1810_, uint8_t v_t_1811_, lean_object* v_h_1812_, lean_object* v_withoutSpacing_1813_){
_start:
{
lean_inc(v_withoutSpacing_1813_);
return v_withoutSpacing_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1814_, lean_object* v_t_1815_, lean_object* v_h_1816_, lean_object* v_withoutSpacing_1817_){
_start:
{
uint8_t v_t_boxed_1818_; lean_object* v_res_1819_; 
v_t_boxed_1818_ = lean_unbox(v_t_1815_);
v_res_1819_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacing_elim(v_motive_1814_, v_t_boxed_1818_, v_h_1816_, v_withoutSpacing_1817_);
lean_dec(v_withoutSpacing_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(lean_object* v_withoutSpacingIfAtomic_1820_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1820_);
return v_withoutSpacingIfAtomic_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg___boxed(lean_object* v_withoutSpacingIfAtomic_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___redArg(v_withoutSpacingIfAtomic_1821_);
lean_dec(v_withoutSpacingIfAtomic_1821_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(lean_object* v_motive_1823_, uint8_t v_t_1824_, lean_object* v_h_1825_, lean_object* v_withoutSpacingIfAtomic_1826_){
_start:
{
lean_inc(v_withoutSpacingIfAtomic_1826_);
return v_withoutSpacingIfAtomic_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim___boxed(lean_object* v_motive_1827_, lean_object* v_t_1828_, lean_object* v_h_1829_, lean_object* v_withoutSpacingIfAtomic_1830_){
_start:
{
uint8_t v_t_boxed_1831_; lean_object* v_res_1832_; 
v_t_boxed_1831_ = lean_unbox(v_t_1828_);
v_res_1832_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withoutSpacingIfAtomic_elim(v_motive_1827_, v_t_boxed_1831_, v_h_1829_, v_withoutSpacingIfAtomic_1830_);
lean_dec(v_withoutSpacingIfAtomic_1830_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1833_){
_start:
{
lean_inc(v_withSpacing_1833_);
return v_withSpacing_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1834_);
lean_dec(v_withSpacing_1834_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(lean_object* v_motive_1836_, uint8_t v_t_1837_, lean_object* v_h_1838_, lean_object* v_withSpacing_1839_){
_start:
{
lean_inc(v_withSpacing_1839_);
return v_withSpacing_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1840_, lean_object* v_t_1841_, lean_object* v_h_1842_, lean_object* v_withSpacing_1843_){
_start:
{
uint8_t v_t_boxed_1844_; lean_object* v_res_1845_; 
v_t_boxed_1844_ = lean_unbox(v_t_1841_);
v_res_1845_ = l_Lean_Fmt_Layouts_Types_PrefixOperatorFormat_withSpacing_elim(v_motive_1840_, v_t_boxed_1844_, v_h_1842_, v_withSpacing_1843_);
lean_dec(v_withSpacing_1843_);
return v_res_1845_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = lean_unsigned_to_nat(16u);
v___x_1848_ = lean_mk_array(v___x_1847_, v___x_1846_);
return v___x_1848_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__0);
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
lean_ctor_set(v___x_1851_, 1, v___x_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(lean_object* v_v_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v_fst_1855_; uint8_t v___x_1856_; 
v___x_1853_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___closed__1);
v___x_1854_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned_goMemoized___redArg(v_v_1852_, v___x_1853_);
v_fst_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_fst_1855_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = lean_unbox(v_fst_1855_);
lean_dec(v_fst_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0___boxed(lean_object* v_v_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_v_1857_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator(lean_object* v_prefixOperatorTk_1860_, lean_object* v_operand_1861_, uint8_t v_format_1862_){
_start:
{
lean_object* v___y_1864_; uint8_t v___y_1876_; uint8_t v___x_1883_; uint8_t v___y_1885_; uint8_t v___y_1888_; 
v___x_1883_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_prefixOperatorTk_1860_);
if (v___x_1883_ == 0)
{
if (v_format_1862_ == 0)
{
goto v___jp_1868_;
}
else
{
if (v___x_1883_ == 0)
{
uint8_t v___x_1889_; 
v___x_1889_ = 1;
if (v_format_1862_ == 1)
{
goto v___jp_1890_;
}
else
{
if (v___x_1883_ == 0)
{
v___y_1888_ = v___x_1883_;
goto v___jp_1887_;
}
else
{
goto v___jp_1890_;
}
}
v___jp_1890_:
{
uint8_t v___x_1891_; 
v___x_1891_ = l_Lean_Fmt_TaggedDoc_isAtomic(v_operand_1861_);
if (v___x_1891_ == 0)
{
uint8_t v___x_1892_; 
lean_inc_ref(v_operand_1861_);
v___x_1892_ = l_Lean_Fmt_TaggedDoc_isSelfDelimited(v_operand_1861_);
v___y_1888_ = v___x_1892_;
goto v___jp_1887_;
}
else
{
v___y_1885_ = v___x_1889_;
goto v___jp_1884_;
}
}
}
else
{
goto v___jp_1868_;
}
}
}
else
{
lean_dec_ref(v_prefixOperatorTk_1860_);
return v_operand_1861_;
}
v___jp_1863_:
{
lean_object* v_doc_1865_; uint8_t v___x_1866_; 
v_doc_1865_ = lean_ctor_get(v_operand_1861_, 0);
lean_inc(v_doc_1865_);
lean_dec_ref(v_operand_1861_);
v___x_1866_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_1865_);
if (v___x_1866_ == 0)
{
return v___y_1864_;
}
else
{
lean_object* v_doc_1867_; 
v_doc_1867_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___y_1864_);
return v_doc_1867_;
}
}
v___jp_1868_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1869_ = lean_unsigned_to_nat(2u);
v___x_1870_ = lean_mk_empty_array_with_capacity(v___x_1869_);
v___x_1871_ = lean_array_push(v___x_1870_, v_prefixOperatorTk_1860_);
lean_inc_ref(v_operand_1861_);
v___x_1872_ = lean_array_push(v___x_1871_, v_operand_1861_);
v___x_1873_ = l_Lean_Fmt_Layouts_atomic(v___x_1872_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1873_);
v___y_1864_ = v___x_1874_;
goto v___jp_1863_;
}
v___jp_1875_:
{
if (v___y_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1877_ = lean_unsigned_to_nat(2u);
v___x_1878_ = lean_mk_empty_array_with_capacity(v___x_1877_);
v___x_1879_ = lean_array_push(v___x_1878_, v_prefixOperatorTk_1860_);
lean_inc_ref(v_operand_1861_);
v___x_1880_ = lean_array_push(v___x_1879_, v_operand_1861_);
v___x_1881_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1880_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1881_);
v___y_1864_ = v___x_1882_;
goto v___jp_1863_;
}
else
{
goto v___jp_1868_;
}
}
v___jp_1884_:
{
uint8_t v___x_1886_; 
lean_inc_ref(v_operand_1861_);
v___x_1886_ = l_Lean_Fmt_TaggedDoc_isRawFallback(v_operand_1861_);
if (v___x_1886_ == 0)
{
v___y_1876_ = v___y_1885_;
goto v___jp_1875_;
}
else
{
v___y_1876_ = v___x_1883_;
goto v___jp_1875_;
}
}
v___jp_1887_:
{
if (v___y_1888_ == 0)
{
v___y_1876_ = v___x_1883_;
goto v___jp_1875_;
}
else
{
v___y_1885_ = v___y_1888_;
goto v___jp_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_prefixOperator___boxed(lean_object* v_prefixOperatorTk_1893_, lean_object* v_operand_1894_, lean_object* v_format_1895_){
_start:
{
uint8_t v_format_boxed_1896_; lean_object* v_res_1897_; 
v_format_boxed_1896_ = lean_unbox(v_format_1895_);
v_res_1897_ = l_Lean_Fmt_Layouts_prefixOperator(v_prefixOperatorTk_1893_, v_operand_1894_, v_format_boxed_1896_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(uint8_t v_x_1898_){
_start:
{
if (v_x_1898_ == 0)
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_unsigned_to_nat(0u);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_unsigned_to_nat(1u);
return v___x_1900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1901_){
_start:
{
uint8_t v_x_boxed_1902_; lean_object* v_res_1903_; 
v_x_boxed_1902_ = lean_unbox(v_x_1901_);
v_res_1903_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorIdx(v_x_boxed_1902_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(lean_object* v_k_1904_){
_start:
{
lean_inc(v_k_1904_);
return v_k_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_k_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___redArg(v_k_1905_);
lean_dec(v_k_1905_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(lean_object* v_motive_1907_, lean_object* v_ctorIdx_1908_, uint8_t v_t_1909_, lean_object* v_h_1910_, lean_object* v_k_1911_){
_start:
{
lean_inc(v_k_1911_);
return v_k_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_1912_, lean_object* v_ctorIdx_1913_, lean_object* v_t_1914_, lean_object* v_h_1915_, lean_object* v_k_1916_){
_start:
{
uint8_t v_t_boxed_1917_; lean_object* v_res_1918_; 
v_t_boxed_1917_ = lean_unbox(v_t_1914_);
v_res_1918_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_ctorElim(v_motive_1912_, v_ctorIdx_1913_, v_t_boxed_1917_, v_h_1915_, v_k_1916_);
lean_dec(v_k_1916_);
lean_dec(v_ctorIdx_1913_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(lean_object* v_withoutSpacing_1919_){
_start:
{
lean_inc(v_withoutSpacing_1919_);
return v_withoutSpacing_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg___boxed(lean_object* v_withoutSpacing_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___redArg(v_withoutSpacing_1920_);
lean_dec(v_withoutSpacing_1920_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(lean_object* v_motive_1922_, uint8_t v_t_1923_, lean_object* v_h_1924_, lean_object* v_withoutSpacing_1925_){
_start:
{
lean_inc(v_withoutSpacing_1925_);
return v_withoutSpacing_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim___boxed(lean_object* v_motive_1926_, lean_object* v_t_1927_, lean_object* v_h_1928_, lean_object* v_withoutSpacing_1929_){
_start:
{
uint8_t v_t_boxed_1930_; lean_object* v_res_1931_; 
v_t_boxed_1930_ = lean_unbox(v_t_1927_);
v_res_1931_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withoutSpacing_elim(v_motive_1926_, v_t_boxed_1930_, v_h_1928_, v_withoutSpacing_1929_);
lean_dec(v_withoutSpacing_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(lean_object* v_withSpacing_1932_){
_start:
{
lean_inc(v_withSpacing_1932_);
return v_withSpacing_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg___boxed(lean_object* v_withSpacing_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___redArg(v_withSpacing_1933_);
lean_dec(v_withSpacing_1933_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(lean_object* v_motive_1935_, uint8_t v_t_1936_, lean_object* v_h_1937_, lean_object* v_withSpacing_1938_){
_start:
{
lean_inc(v_withSpacing_1938_);
return v_withSpacing_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim___boxed(lean_object* v_motive_1939_, lean_object* v_t_1940_, lean_object* v_h_1941_, lean_object* v_withSpacing_1942_){
_start:
{
uint8_t v_t_boxed_1943_; lean_object* v_res_1944_; 
v_t_boxed_1943_ = lean_unbox(v_t_1940_);
v_res_1944_ = l_Lean_Fmt_Layouts_Types_PostfixOperatorFormat_withSpacing_elim(v_motive_1939_, v_t_boxed_1943_, v_h_1941_, v_withSpacing_1942_);
lean_dec(v_withSpacing_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator(lean_object* v_operand_1945_, lean_object* v_postfixOperatorTk_1946_, uint8_t v_format_1947_){
_start:
{
uint8_t v___x_1955_; 
v___x_1955_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_postfixOperatorTk_1946_);
if (v___x_1955_ == 0)
{
if (v_format_1947_ == 1)
{
goto v___jp_1948_;
}
else
{
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1956_ = lean_unsigned_to_nat(2u);
v___x_1957_ = lean_mk_empty_array_with_capacity(v___x_1956_);
v___x_1958_ = lean_array_push(v___x_1957_, v_operand_1945_);
v___x_1959_ = lean_array_push(v___x_1958_, v_postfixOperatorTk_1946_);
v___x_1960_ = l_Lean_Fmt_Layouts_atomic(v___x_1959_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1960_);
return v___x_1961_;
}
else
{
goto v___jp_1948_;
}
}
}
else
{
lean_dec_ref(v_postfixOperatorTk_1946_);
return v_operand_1945_;
}
v___jp_1948_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1949_ = lean_unsigned_to_nat(2u);
v___x_1950_ = lean_mk_empty_array_with_capacity(v___x_1949_);
v___x_1951_ = lean_array_push(v___x_1950_, v_operand_1945_);
v___x_1952_ = lean_array_push(v___x_1951_, v_postfixOperatorTk_1946_);
v___x_1953_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_1952_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l_Lean_Fmt_TaggedDoc_nested(v___x_1953_);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_postfixOperator___boxed(lean_object* v_operand_1962_, lean_object* v_postfixOperatorTk_1963_, lean_object* v_format_1964_){
_start:
{
uint8_t v_format_boxed_1965_; lean_object* v_res_1966_; 
v_format_boxed_1965_ = lean_unbox(v_format_1964_);
v_res_1966_ = l_Lean_Fmt_Layouts_postfixOperator(v_operand_1962_, v_postfixOperatorTk_1963_, v_format_boxed_1965_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(lean_object* v_x_1967_){
_start:
{
if (lean_obj_tag(v_x_1967_) == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_unsigned_to_nat(0u);
return v___x_1968_;
}
else
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_unsigned_to_nat(1u);
return v___x_1969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx___boxed(lean_object* v_x_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorIdx(v_x_1970_);
lean_dec_ref(v_x_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(lean_object* v_t_1972_, lean_object* v_k_1973_){
_start:
{
if (lean_obj_tag(v_t_1972_) == 0)
{
uint8_t v_hardNestedFirstOperand_1974_; uint8_t v_trailingOperator_1975_; uint8_t v_spacing_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_hardNestedFirstOperand_1974_ = lean_ctor_get_uint8(v_t_1972_, 0);
v_trailingOperator_1975_ = lean_ctor_get_uint8(v_t_1972_, 1);
v_spacing_1976_ = lean_ctor_get_uint8(v_t_1972_, 2);
v___x_1977_ = lean_box(v_hardNestedFirstOperand_1974_);
v___x_1978_ = lean_box(v_trailingOperator_1975_);
v___x_1979_ = lean_box(v_spacing_1976_);
v___x_1980_ = lean_apply_3(v_k_1973_, v___x_1977_, v___x_1978_, v___x_1979_);
return v___x_1980_;
}
else
{
uint8_t v_hardNestedFirstOperand_1981_; uint8_t v_trailingOperator_1982_; uint8_t v_spacing_1983_; uint8_t v_alignedOperators_1984_; uint8_t v_separateFinalOperand_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_hardNestedFirstOperand_1981_ = lean_ctor_get_uint8(v_t_1972_, 0);
v_trailingOperator_1982_ = lean_ctor_get_uint8(v_t_1972_, 1);
v_spacing_1983_ = lean_ctor_get_uint8(v_t_1972_, 2);
v_alignedOperators_1984_ = lean_ctor_get_uint8(v_t_1972_, 3);
v_separateFinalOperand_1985_ = lean_ctor_get_uint8(v_t_1972_, 4);
v___x_1986_ = lean_box(v_hardNestedFirstOperand_1981_);
v___x_1987_ = lean_box(v_trailingOperator_1982_);
v___x_1988_ = lean_box(v_spacing_1983_);
v___x_1989_ = lean_box(v_alignedOperators_1984_);
v___x_1990_ = lean_box(v_separateFinalOperand_1985_);
v___x_1991_ = lean_apply_5(v_k_1973_, v___x_1986_, v___x_1987_, v___x_1988_, v___x_1989_, v___x_1990_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg___boxed(lean_object* v_t_1992_, lean_object* v_k_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1992_, v_k_1993_);
lean_dec_ref(v_t_1992_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(lean_object* v_motive_1995_, lean_object* v_ctorIdx_1996_, lean_object* v_t_1997_, lean_object* v_h_1998_, lean_object* v_k_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_1997_, v_k_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___boxed(lean_object* v_motive_2001_, lean_object* v_ctorIdx_2002_, lean_object* v_t_2003_, lean_object* v_h_2004_, lean_object* v_k_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim(v_motive_2001_, v_ctorIdx_2002_, v_t_2003_, v_h_2004_, v_k_2005_);
lean_dec_ref(v_t_2003_);
lean_dec(v_ctorIdx_2002_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(lean_object* v_t_2007_, lean_object* v_dense_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2007_, v_dense_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg___boxed(lean_object* v_t_2010_, lean_object* v_dense_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___redArg(v_t_2010_, v_dense_2011_);
lean_dec_ref(v_t_2010_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(lean_object* v_motive_2013_, lean_object* v_t_2014_, lean_object* v_h_2015_, lean_object* v_dense_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2014_, v_dense_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim___boxed(lean_object* v_motive_2018_, lean_object* v_t_2019_, lean_object* v_h_2020_, lean_object* v_dense_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_dense_elim(v_motive_2018_, v_t_2019_, v_h_2020_, v_dense_2021_);
lean_dec_ref(v_t_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(lean_object* v_t_2023_, lean_object* v_sparse_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2023_, v_sparse_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg___boxed(lean_object* v_t_2026_, lean_object* v_sparse_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___redArg(v_t_2026_, v_sparse_2027_);
lean_dec_ref(v_t_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(lean_object* v_motive_2029_, lean_object* v_t_2030_, lean_object* v_h_2031_, lean_object* v_sparse_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_ctorElim___redArg(v_t_2030_, v_sparse_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim___boxed(lean_object* v_motive_2034_, lean_object* v_t_2035_, lean_object* v_h_2036_, lean_object* v_sparse_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_sparse_elim(v_motive_2034_, v_t_2035_, v_h_2036_, v_sparse_2037_);
lean_dec_ref(v_t_2035_);
return v_res_2038_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(lean_object* v_x_2039_){
_start:
{
uint8_t v_hardNestedFirstOperand_2040_; 
v_hardNestedFirstOperand_2040_ = lean_ctor_get_uint8(v_x_2039_, 0);
return v_hardNestedFirstOperand_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand___boxed(lean_object* v_x_2041_){
_start:
{
uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_res_2042_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_hardNestedFirstOperand(v_x_2041_);
lean_dec_ref(v_x_2041_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(lean_object* v_x_2044_){
_start:
{
uint8_t v_trailingOperator_2045_; 
v_trailingOperator_2045_ = lean_ctor_get_uint8(v_x_2044_, 1);
return v_trailingOperator_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator___boxed(lean_object* v_x_2046_){
_start:
{
uint8_t v_res_2047_; lean_object* v_r_2048_; 
v_res_2047_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_trailingOperator(v_x_2046_);
lean_dec_ref(v_x_2046_);
v_r_2048_ = lean_box(v_res_2047_);
return v_r_2048_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(lean_object* v_x_2049_){
_start:
{
uint8_t v_spacing_2050_; 
v_spacing_2050_ = lean_ctor_get_uint8(v_x_2049_, 2);
return v_spacing_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing___boxed(lean_object* v_x_2051_){
_start:
{
uint8_t v_res_2052_; lean_object* v_r_2053_; 
v_res_2052_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_spacing(v_x_2051_);
lean_dec_ref(v_x_2051_);
v_r_2053_ = lean_box(v_res_2052_);
return v_r_2053_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(lean_object* v_x_2054_){
_start:
{
if (lean_obj_tag(v_x_2054_) == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = 0;
return v___x_2055_;
}
else
{
uint8_t v_trailingOperator_2056_; 
v_trailingOperator_2056_ = lean_ctor_get_uint8(v_x_2054_, 1);
if (v_trailingOperator_2056_ == 0)
{
uint8_t v_alignedOperators_2057_; 
v_alignedOperators_2057_ = lean_ctor_get_uint8(v_x_2054_, 3);
return v_alignedOperators_2057_;
}
else
{
uint8_t v___x_2058_; 
v___x_2058_ = 0;
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators___boxed(lean_object* v_x_2059_){
_start:
{
uint8_t v_res_2060_; lean_object* v_r_2061_; 
v_res_2060_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_x_2059_);
lean_dec_ref(v_x_2059_);
v_r_2061_ = lean_box(v_res_2060_);
return v_r_2061_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(lean_object* v_x_2062_){
_start:
{
if (lean_obj_tag(v_x_2062_) == 0)
{
uint8_t v___x_2063_; 
v___x_2063_ = 0;
return v___x_2063_;
}
else
{
uint8_t v_trailingOperator_2064_; 
v_trailingOperator_2064_ = lean_ctor_get_uint8(v_x_2062_, 1);
if (v_trailingOperator_2064_ == 0)
{
uint8_t v_separateFinalOperand_2065_; 
v_separateFinalOperand_2065_ = lean_ctor_get_uint8(v_x_2062_, 4);
return v_separateFinalOperand_2065_;
}
else
{
uint8_t v___x_2066_; 
v___x_2066_ = 0;
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand___boxed(lean_object* v_x_2067_){
_start:
{
uint8_t v_res_2068_; lean_object* v_r_2069_; 
v_res_2068_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_x_2067_);
lean_dec_ref(v_x_2067_);
v_r_2069_ = lean_box(v_res_2068_);
return v_r_2069_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_permitDenseLayout(lean_object* v_doc_2070_, uint8_t v_respectPseudoAlignment_2071_){
_start:
{
if (v_respectPseudoAlignment_2071_ == 0)
{
lean_object* v_doc_2072_; uint8_t v___x_2073_; 
v_doc_2072_ = lean_ctor_get(v_doc_2070_, 0);
lean_inc(v_doc_2072_);
lean_dec_ref(v_doc_2070_);
v___x_2073_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2072_);
if (v___x_2073_ == 0)
{
uint8_t v___x_2074_; 
v___x_2074_ = 1;
return v___x_2074_;
}
else
{
return v_respectPseudoAlignment_2071_;
}
}
else
{
uint8_t v___x_2075_; 
lean_inc_ref(v_doc_2070_);
v___x_2075_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_doc_2070_);
if (v___x_2075_ == 0)
{
lean_object* v_doc_2076_; uint8_t v___x_2077_; 
v_doc_2076_ = lean_ctor_get(v_doc_2070_, 0);
lean_inc(v_doc_2076_);
lean_dec_ref(v_doc_2070_);
v___x_2077_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2076_);
if (v___x_2077_ == 0)
{
return v_respectPseudoAlignment_2071_;
}
else
{
return v___x_2075_;
}
}
else
{
uint8_t v___x_2078_; 
lean_dec_ref(v_doc_2070_);
v___x_2078_ = 0;
return v___x_2078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_permitDenseLayout___boxed(lean_object* v_doc_2079_, lean_object* v_respectPseudoAlignment_2080_){
_start:
{
uint8_t v_respectPseudoAlignment_boxed_2081_; uint8_t v_res_2082_; lean_object* v_r_2083_; 
v_respectPseudoAlignment_boxed_2081_ = lean_unbox(v_respectPseudoAlignment_2080_);
v_res_2082_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_doc_2079_, v_respectPseudoAlignment_boxed_2081_);
v_r_2083_ = lean_box(v_res_2082_);
return v_r_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(lean_object* v_format_2084_, lean_object* v_docs_2085_){
_start:
{
uint8_t v___y_2087_; uint8_t v_spacing_2090_; 
v_spacing_2090_ = lean_ctor_get_uint8(v_format_2084_, 2);
v___y_2087_ = v_spacing_2090_;
goto v___jp_2086_;
v___jp_2086_:
{
if (v___y_2087_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Fmt_Layouts_atomic(v_docs_2085_);
return v___x_2088_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Fmt_Layouts_spacedAtomic(v_docs_2085_);
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat___boxed(lean_object* v_format_2091_, lean_object* v_docs_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2091_, v_docs_2092_);
lean_dec_ref(v_docs_2092_);
lean_dec_ref(v_format_2091_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(lean_object* v_msg_2094_){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = l_Lean_Fmt_TaggedDoc_instInhabitedSticky_default;
v___x_2096_ = lean_panic_fn_borrowed(v___x_2095_, v_msg_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(uint8_t v_a_2097_, lean_object* v_as_2098_, size_t v_i_2099_, size_t v_stop_2100_){
_start:
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_usize_dec_eq(v_i_2099_, v_stop_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; uint8_t v___x_2103_; uint8_t v___x_2104_; 
v___x_2102_ = lean_array_uget_borrowed(v_as_2098_, v_i_2099_);
v___x_2103_ = lean_unbox(v___x_2102_);
v___x_2104_ = l_Lean_Fmt_TaggedDoc_instBEqStickynessKind_beq(v_a_2097_, v___x_2103_);
if (v___x_2104_ == 0)
{
size_t v___x_2105_; size_t v___x_2106_; 
v___x_2105_ = ((size_t)1ULL);
v___x_2106_ = lean_usize_add(v_i_2099_, v___x_2105_);
v_i_2099_ = v___x_2106_;
goto _start;
}
else
{
return v___x_2104_;
}
}
else
{
uint8_t v___x_2108_; 
v___x_2108_ = 0;
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0___boxed(lean_object* v_a_2109_, lean_object* v_as_2110_, lean_object* v_i_2111_, lean_object* v_stop_2112_){
_start:
{
uint8_t v_a_boxed_2113_; size_t v_i_boxed_2114_; size_t v_stop_boxed_2115_; uint8_t v_res_2116_; lean_object* v_r_2117_; 
v_a_boxed_2113_ = lean_unbox(v_a_2109_);
v_i_boxed_2114_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_stop_boxed_2115_ = lean_unbox_usize(v_stop_2112_);
lean_dec(v_stop_2112_);
v_res_2116_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_boxed_2113_, v_as_2110_, v_i_boxed_2114_, v_stop_boxed_2115_);
lean_dec_ref(v_as_2110_);
v_r_2117_ = lean_box(v_res_2116_);
return v_r_2117_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(lean_object* v_as_2118_, uint8_t v_a_2119_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = lean_unsigned_to_nat(0u);
v___x_2121_ = lean_array_get_size(v_as_2118_);
v___x_2122_ = lean_nat_dec_lt(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
return v___x_2122_;
}
else
{
if (v___x_2122_ == 0)
{
return v___x_2122_;
}
else
{
size_t v___x_2123_; size_t v___x_2124_; uint8_t v___x_2125_; 
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = lean_usize_of_nat(v___x_2121_);
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0_spec__0(v_a_2119_, v_as_2118_, v___x_2123_, v___x_2124_);
return v___x_2125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0___boxed(lean_object* v_as_2126_, lean_object* v_a_2127_){
_start:
{
uint8_t v_a_boxed_2128_; uint8_t v_res_2129_; lean_object* v_r_2130_; 
v_a_boxed_2128_ = lean_unbox(v_a_2127_);
v_res_2129_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_as_2126_, v_a_boxed_2128_);
lean_dec_ref(v_as_2126_);
v_r_2130_ = lean_box(v_res_2129_);
return v_r_2130_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__2));
v___x_2135_ = lean_unsigned_to_nat(14u);
v___x_2136_ = lean_unsigned_to_nat(22u);
v___x_2137_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__1));
v___x_2138_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__0));
v___x_2139_ = l_mkPanicMessageWithDecl(v___x_2138_, v___x_2137_, v___x_2136_, v___x_2135_, v___x_2134_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(lean_object* v_format_2140_, lean_object* v_doc_2141_, lean_object* v_lastOperand_2142_, uint8_t v_isTailless_2143_, lean_object* v_combinedChain_2144_, lean_object* v_eligibleKinds_2145_){
_start:
{
lean_object* v___x_2146_; uint8_t v___y_2148_; lean_object* v___y_2149_; uint8_t v___y_2170_; uint8_t v_trailingOperator_2183_; 
v___x_2146_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2183_ = lean_ctor_get_uint8(v_format_2140_, 1);
v___y_2170_ = v_trailingOperator_2183_;
goto v___jp_2169_;
v___jp_2147_:
{
lean_object* v_stickyVariant_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_stickyVariant_2150_ = lean_ctor_get(v___y_2149_, 0);
v___x_2151_ = lean_array_get_size(v_combinedChain_2144_);
v___x_2152_ = lean_unsigned_to_nat(1u);
v___x_2153_ = lean_nat_sub(v___x_2151_, v___x_2152_);
lean_inc_ref(v_stickyVariant_2150_);
v___x_2154_ = lean_array_set(v_combinedChain_2144_, v___x_2153_, v_stickyVariant_2150_);
lean_dec(v___x_2153_);
lean_inc_ref(v___x_2154_);
v___x_2155_ = lean_array_pop(v___x_2154_);
v___x_2156_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2140_, v___x_2155_);
lean_dec_ref(v___x_2155_);
v___x_2157_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_2156_);
v___x_2158_ = lean_array_get_size(v___x_2154_);
v___x_2159_ = lean_nat_sub(v___x_2158_, v___x_2152_);
v___x_2160_ = lean_array_get(v___x_2146_, v___x_2154_, v___x_2159_);
lean_dec(v___x_2159_);
lean_dec_ref(v___x_2154_);
v___x_2161_ = lean_unsigned_to_nat(2u);
v___x_2162_ = lean_mk_empty_array_with_capacity(v___x_2161_);
v___x_2163_ = lean_array_push(v___x_2162_, v___x_2157_);
v___x_2164_ = lean_array_push(v___x_2163_, v___x_2160_);
v___x_2165_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2140_, v___x_2164_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_2149_, v___y_2148_);
lean_dec_ref(v___y_2149_);
v___x_2167_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_doc_2141_, v___x_2165_, v___x_2166_);
lean_dec(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
v___jp_2169_:
{
if (v___y_2170_ == 0)
{
lean_object* v___x_2171_; 
lean_dec_ref(v_combinedChain_2144_);
lean_dec_ref(v_lastOperand_2142_);
lean_dec_ref(v_doc_2141_);
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
else
{
if (v_isTailless_2143_ == 0)
{
lean_object* v___x_2172_; 
lean_inc_ref(v_lastOperand_2142_);
v___x_2172_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v_lastOperand_2142_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v___x_2173_; 
lean_dec_ref(v_combinedChain_2144_);
lean_dec_ref(v_lastOperand_2142_);
lean_dec_ref(v_doc_2141_);
v___x_2173_ = lean_box(0);
return v___x_2173_;
}
else
{
lean_object* v_val_2174_; uint8_t v___x_2175_; uint8_t v___x_2176_; 
v_val_2174_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_val_2174_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2175_ = lean_unbox(v_val_2174_);
lean_dec(v_val_2174_);
v___x_2176_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_2145_, v___x_2175_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref(v_combinedChain_2144_);
lean_dec_ref(v_lastOperand_2142_);
lean_dec_ref(v_doc_2141_);
v___x_2177_ = lean_box(0);
return v___x_2177_;
}
else
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_lastOperand_2142_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_2180_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_2179_);
v___y_2148_ = v___x_2176_;
v___y_2149_ = v___x_2180_;
goto v___jp_2147_;
}
else
{
lean_object* v_val_2181_; 
v_val_2181_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v___x_2178_, 1);
v___y_2148_ = v___x_2176_;
v___y_2149_ = v_val_2181_;
goto v___jp_2147_;
}
}
}
}
else
{
lean_object* v___x_2182_; 
lean_dec_ref(v_combinedChain_2144_);
lean_dec_ref(v_lastOperand_2142_);
lean_dec_ref(v_doc_2141_);
v___x_2182_ = lean_box(0);
return v___x_2182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___boxed(lean_object* v_format_2184_, lean_object* v_doc_2185_, lean_object* v_lastOperand_2186_, lean_object* v_isTailless_2187_, lean_object* v_combinedChain_2188_, lean_object* v_eligibleKinds_2189_){
_start:
{
uint8_t v_isTailless_boxed_2190_; lean_object* v_res_2191_; 
v_isTailless_boxed_2190_ = lean_unbox(v_isTailless_2187_);
v_res_2191_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2184_, v_doc_2185_, v_lastOperand_2186_, v_isTailless_boxed_2190_, v_combinedChain_2188_, v_eligibleKinds_2189_);
lean_dec_ref(v_eligibleKinds_2189_);
lean_dec_ref(v_format_2184_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(lean_object* v_format_2192_, lean_object* v_doc_2193_, lean_object* v_lastOperand_2194_, uint8_t v_isTailless_2195_, lean_object* v_combinedChain_2196_){
_start:
{
if (lean_obj_tag(v_format_2192_) == 0)
{
if (v_isTailless_2195_ == 0)
{
uint8_t v_trailingOperator_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; 
v_trailingOperator_2197_ = lean_ctor_get_uint8(v_format_2192_, 1);
v___x_2198_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2199_ = 1;
if (v_trailingOperator_2197_ == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v___x_2217_ = lean_array_get_size(v_combinedChain_2196_);
v___x_2218_ = lean_unsigned_to_nat(2u);
v___x_2219_ = lean_nat_dec_eq(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; 
lean_dec_ref(v_combinedChain_2196_);
lean_dec_ref(v_lastOperand_2194_);
lean_dec_ref(v_doc_2193_);
v___x_2220_ = lean_box(0);
return v___x_2220_;
}
else
{
goto v___jp_2200_;
}
}
else
{
goto v___jp_2200_;
}
v___jp_2200_:
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_lastOperand_2194_, v___x_2199_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
lean_dec_ref(v_combinedChain_2196_);
lean_dec_ref(v_doc_2193_);
v___x_2202_ = lean_box(0);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_inc_ref(v_combinedChain_2196_);
v___x_2203_ = lean_array_pop(v_combinedChain_2196_);
v___x_2204_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2192_, v___x_2203_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_2204_);
v___x_2206_ = lean_array_get_size(v_combinedChain_2196_);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_sub(v___x_2206_, v___x_2207_);
v___x_2209_ = lean_array_get(v___x_2198_, v_combinedChain_2196_, v___x_2208_);
lean_dec(v___x_2208_);
lean_dec_ref(v_combinedChain_2196_);
v___x_2210_ = lean_unsigned_to_nat(2u);
v___x_2211_ = lean_mk_empty_array_with_capacity(v___x_2210_);
v___x_2212_ = lean_array_push(v___x_2211_, v___x_2205_);
v___x_2213_ = lean_array_push(v___x_2212_, v___x_2209_);
v___x_2214_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2192_, v___x_2213_);
lean_dec_ref(v___x_2213_);
v___x_2215_ = l_Lean_Fmt_TaggedDoc_fallbackOnHeight(v_doc_2193_, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
}
else
{
lean_object* v___x_2221_; 
lean_dec_ref(v_combinedChain_2196_);
lean_dec_ref(v_lastOperand_2194_);
lean_dec_ref(v_doc_2193_);
v___x_2221_ = lean_box(0);
return v___x_2221_;
}
}
else
{
lean_object* v___x_2222_; 
lean_dec_ref(v_combinedChain_2196_);
lean_dec_ref(v_lastOperand_2194_);
lean_dec_ref(v_doc_2193_);
v___x_2222_ = lean_box(0);
return v___x_2222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f___boxed(lean_object* v_format_2223_, lean_object* v_doc_2224_, lean_object* v_lastOperand_2225_, lean_object* v_isTailless_2226_, lean_object* v_combinedChain_2227_){
_start:
{
uint8_t v_isTailless_boxed_2228_; lean_object* v_res_2229_; 
v_isTailless_boxed_2228_ = lean_unbox(v_isTailless_2226_);
v_res_2229_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2223_, v_doc_2224_, v_lastOperand_2225_, v_isTailless_boxed_2228_, v_combinedChain_2227_);
lean_dec_ref(v_format_2223_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(lean_object* v_snd_2230_, lean_object* v___x_2231_, lean_object* v_____r_2232_, lean_object* v_normalized_2233_){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = lean_nat_add(v_snd_2230_, v___x_2231_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_normalized_2233_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0___boxed(lean_object* v_snd_2237_, lean_object* v___x_2238_, lean_object* v_____r_2239_, lean_object* v_normalized_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2237_, v___x_2238_, v_____r_2239_, v_normalized_2240_);
lean_dec(v___x_2238_);
lean_dec(v_snd_2237_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(lean_object* v___x_2242_, lean_object* v_chain_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___y_2246_; lean_object* v_fst_2250_; lean_object* v_snd_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2278_; 
v_fst_2250_ = lean_ctor_get(v_a_2244_, 0);
v_snd_2251_ = lean_ctor_get(v_a_2244_, 1);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_a_2244_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2253_ = v_a_2244_;
v_isShared_2254_ = v_isSharedCheck_2278_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_snd_2251_);
lean_inc(v_fst_2250_);
lean_dec(v_a_2244_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2278_;
goto v_resetjp_2252_;
}
v___jp_2245_:
{
if (lean_obj_tag(v___y_2246_) == 0)
{
lean_object* v_a_2247_; 
v_a_2247_ = lean_ctor_get(v___y_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___y_2246_, 1);
return v_a_2247_;
}
else
{
lean_object* v_a_2248_; 
v_a_2248_ = lean_ctor_get(v___y_2246_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___y_2246_, 1);
v_a_2244_ = v_a_2248_;
goto _start;
}
}
v_resetjp_2252_:
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_nat_dec_lt(v_snd_2251_, v___x_2242_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2257_; 
if (v_isShared_2254_ == 0)
{
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_fst_2250_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_snd_2251_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2259_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2260_ = lean_array_get_borrowed(v___x_2259_, v_chain_2243_, v_snd_2251_);
v___x_2261_ = lean_unsigned_to_nat(1u);
v___x_2262_ = lean_nat_add(v_snd_2251_, v___x_2261_);
v___x_2263_ = lean_array_get_size(v_chain_2243_);
v___x_2264_ = lean_nat_dec_lt(v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_dec(v___x_2262_);
lean_inc(v___x_2260_);
v___x_2265_ = lean_array_push(v_fst_2250_, v___x_2260_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 0, v___x_2265_);
v___x_2267_ = v___x_2253_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_snd_2251_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
lean_del_object(v___x_2253_);
v___x_2269_ = lean_unsigned_to_nat(2u);
v___x_2270_ = lean_array_fget_borrowed(v_chain_2243_, v___x_2262_);
lean_dec(v___x_2262_);
v___x_2271_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_inc(v___x_2260_);
v___x_2272_ = lean_array_push(v_fst_2250_, v___x_2260_);
lean_inc(v___x_2270_);
v___x_2273_ = lean_array_push(v___x_2272_, v___x_2270_);
v___x_2274_ = lean_box(0);
v___x_2275_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2251_, v___x_2269_, v___x_2274_, v___x_2273_);
lean_dec(v_snd_2251_);
v___y_2246_ = v___x_2275_;
goto v___jp_2245_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_box(0);
v___x_2277_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2251_, v___x_2269_, v___x_2276_, v_fst_2250_);
lean_dec(v_snd_2251_);
v___y_2246_ = v___x_2277_;
goto v___jp_2245_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg___boxed(lean_object* v___x_2279_, lean_object* v_chain_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2279_, v_chain_2280_, v_a_2281_);
lean_dec_ref(v_chain_2280_);
lean_dec(v___x_2279_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(lean_object* v___x_2283_, lean_object* v_chain_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v___y_2287_; lean_object* v_fst_2291_; lean_object* v_snd_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2319_; 
v_fst_2291_ = lean_ctor_get(v_a_2285_, 0);
v_snd_2292_ = lean_ctor_get(v_a_2285_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_a_2285_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2294_ = v_a_2285_;
v_isShared_2295_ = v_isSharedCheck_2319_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_snd_2292_);
lean_inc(v_fst_2291_);
lean_dec(v_a_2285_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2319_;
goto v_resetjp_2293_;
}
v___jp_2286_:
{
if (lean_obj_tag(v___y_2287_) == 0)
{
lean_object* v_a_2288_; 
v_a_2288_ = lean_ctor_get(v___y_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___y_2287_, 1);
return v_a_2288_;
}
else
{
lean_object* v_a_2289_; 
v_a_2289_ = lean_ctor_get(v___y_2287_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___y_2287_, 1);
v_a_2285_ = v_a_2289_;
goto _start;
}
}
v_resetjp_2293_:
{
uint8_t v___x_2296_; 
v___x_2296_ = lean_nat_dec_lt(v_snd_2292_, v___x_2283_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2298_; 
if (v_isShared_2295_ == 0)
{
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_snd_2292_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v___x_2300_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2301_ = lean_array_get_borrowed(v___x_2300_, v_chain_2284_, v_snd_2292_);
v___x_2302_ = lean_unsigned_to_nat(1u);
v___x_2303_ = lean_nat_add(v_snd_2292_, v___x_2302_);
v___x_2304_ = lean_array_get_size(v_chain_2284_);
v___x_2305_ = lean_nat_dec_lt(v___x_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2306_; lean_object* v___x_2308_; 
lean_dec(v___x_2303_);
lean_inc(v___x_2301_);
v___x_2306_ = lean_array_push(v_fst_2291_, v___x_2301_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2306_);
v___x_2308_ = v___x_2294_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_snd_2292_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
lean_del_object(v___x_2294_);
v___x_2310_ = lean_unsigned_to_nat(2u);
v___x_2311_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_2301_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2312_ = lean_array_fget_borrowed(v_chain_2284_, v___x_2303_);
lean_dec(v___x_2303_);
lean_inc(v___x_2301_);
v___x_2313_ = lean_array_push(v_fst_2291_, v___x_2301_);
lean_inc(v___x_2312_);
v___x_2314_ = lean_array_push(v___x_2313_, v___x_2312_);
v___x_2315_ = lean_box(0);
v___x_2316_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2292_, v___x_2310_, v___x_2315_, v___x_2314_);
lean_dec(v_snd_2292_);
v___y_2287_ = v___x_2316_;
goto v___jp_2286_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec(v___x_2303_);
v___x_2317_ = lean_box(0);
v___x_2318_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___lam__0(v_snd_2292_, v___x_2310_, v___x_2317_, v_fst_2291_);
lean_dec(v_snd_2292_);
v___y_2287_ = v___x_2318_;
goto v___jp_2286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg___boxed(lean_object* v___x_2320_, lean_object* v_chain_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2320_, v_chain_2321_, v_a_2322_);
lean_dec_ref(v_chain_2321_);
lean_dec(v___x_2320_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(lean_object* v_format_2332_, lean_object* v_chain_2333_){
_start:
{
lean_object* v___y_2335_; lean_object* v___y_2336_; lean_object* v___y_2337_; uint8_t v___y_2338_; uint8_t v___y_2339_; lean_object* v___y_2340_; lean_object* v___y_2356_; lean_object* v___y_2357_; uint8_t v___y_2358_; lean_object* v___y_2359_; uint8_t v___y_2360_; lean_object* v___y_2361_; lean_object* v___f_2376_; lean_object* v___x_2377_; lean_object* v_chainSizeBeforeSuffixTrim_2378_; lean_object* v_chain_2379_; lean_object* v_chainSizeBeforePrefixTrim_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___y_2386_; lean_object* v___y_2387_; uint8_t v___y_2388_; uint8_t v___y_2389_; uint8_t v___y_2390_; lean_object* v___y_2402_; lean_object* v___y_2403_; uint8_t v___y_2404_; uint8_t v___y_2405_; uint8_t v___y_2410_; uint8_t v___x_2420_; 
v___f_2376_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__0));
v___x_2377_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_chainSizeBeforeSuffixTrim_2378_ = lean_array_get_size(v_chain_2333_);
v_chain_2379_ = l_Array_popWhile___redArg(v___f_2376_, v_chain_2333_);
v_chainSizeBeforePrefixTrim_2380_ = lean_array_get_size(v_chain_2379_);
v___x_2381_ = lean_nat_sub(v_chainSizeBeforeSuffixTrim_2378_, v_chainSizeBeforePrefixTrim_2380_);
v___x_2382_ = lean_unsigned_to_nat(2u);
v___x_2383_ = lean_nat_mod(v___x_2381_, v___x_2382_);
lean_dec(v___x_2381_);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_nat_dec_eq(v___x_2383_, v___x_2384_);
lean_dec(v___x_2383_);
if (v___x_2420_ == 0)
{
uint8_t v___x_2421_; 
v___x_2421_ = 1;
v___y_2410_ = v___x_2421_;
goto v___jp_2409_;
}
else
{
uint8_t v___x_2422_; 
v___x_2422_ = 0;
v___y_2410_ = v___x_2422_;
goto v___jp_2409_;
}
v___jp_2334_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v_fst_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2353_; 
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___y_2336_);
lean_ctor_set(v___x_2341_, 1, v___y_2340_);
v___x_2342_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___y_2337_, v___y_2335_, v___x_2341_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2337_);
v_fst_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; 
v_unused_2354_ = lean_ctor_get(v___x_2342_, 1);
lean_dec(v_unused_2354_);
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2353_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_fst_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2353_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v___x_2347_ = lean_box(v___y_2338_);
v___x_2348_ = lean_box(v___y_2339_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 1, v___x_2348_);
lean_ctor_set(v___x_2345_, 0, v___x_2347_);
v___x_2350_ = v___x_2345_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; 
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_fst_2343_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
return v___x_2351_;
}
}
}
v___jp_2355_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v_fst_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2374_; 
v___x_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___y_2359_);
lean_ctor_set(v___x_2362_, 1, v___y_2361_);
v___x_2363_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___y_2357_, v___y_2356_, v___x_2362_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2357_);
v_fst_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___x_2363_, 1);
lean_dec(v_unused_2375_);
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_fst_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2374_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2368_ = lean_box(v___y_2358_);
v___x_2369_ = lean_box(v___y_2360_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2369_);
lean_ctor_set(v___x_2366_, 0, v___x_2368_);
v___x_2371_ = v___x_2366_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; 
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_fst_2364_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
return v___x_2372_;
}
}
}
v___jp_2385_:
{
if (v___y_2390_ == 0)
{
if (v___y_2388_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2391_ = lean_array_get_borrowed(v___x_2377_, v___y_2386_, v___x_2384_);
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_mk_empty_array_with_capacity(v___x_2392_);
lean_inc(v___x_2391_);
v___x_2394_ = lean_array_push(v___x_2393_, v___x_2391_);
v___y_2356_ = v___y_2386_;
v___y_2357_ = v___y_2387_;
v___y_2358_ = v___y_2388_;
v___y_2359_ = v___x_2394_;
v___y_2360_ = v___y_2389_;
v___y_2361_ = v___x_2392_;
goto v___jp_2355_;
}
else
{
lean_object* v___x_2395_; 
v___x_2395_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2356_ = v___y_2386_;
v___y_2357_ = v___y_2387_;
v___y_2358_ = v___y_2388_;
v___y_2359_ = v___x_2395_;
v___y_2360_ = v___y_2389_;
v___y_2361_ = v___x_2384_;
goto v___jp_2355_;
}
}
else
{
if (v___y_2388_ == 0)
{
lean_object* v___x_2396_; 
v___x_2396_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2335_ = v___y_2386_;
v___y_2336_ = v___x_2396_;
v___y_2337_ = v___y_2387_;
v___y_2338_ = v___y_2388_;
v___y_2339_ = v___y_2389_;
v___y_2340_ = v___x_2384_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = lean_array_get_borrowed(v___x_2377_, v___y_2386_, v___x_2384_);
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_mk_empty_array_with_capacity(v___x_2398_);
lean_inc(v___x_2397_);
v___x_2400_ = lean_array_push(v___x_2399_, v___x_2397_);
v___y_2335_ = v___y_2386_;
v___y_2336_ = v___x_2400_;
v___y_2337_ = v___y_2387_;
v___y_2338_ = v___y_2388_;
v___y_2339_ = v___y_2389_;
v___y_2340_ = v___x_2398_;
goto v___jp_2334_;
}
}
}
v___jp_2401_:
{
uint8_t v___x_2406_; 
v___x_2406_ = lean_nat_dec_eq(v___y_2403_, v___x_2384_);
if (v___x_2406_ == 0)
{
uint8_t v_trailingOperator_2407_; 
v_trailingOperator_2407_ = lean_ctor_get_uint8(v_format_2332_, 1);
v___y_2386_ = v___y_2402_;
v___y_2387_ = v___y_2403_;
v___y_2388_ = v___y_2405_;
v___y_2389_ = v___y_2404_;
v___y_2390_ = v_trailingOperator_2407_;
goto v___jp_2385_;
}
else
{
lean_object* v___x_2408_; 
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
v___x_2408_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___closed__2));
return v___x_2408_;
}
}
v___jp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v_chain_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2411_ = l_Array_reverse___redArg(v_chain_2379_);
v___x_2412_ = l_Array_popWhile___redArg(v___f_2376_, v___x_2411_);
v_chain_2413_ = l_Array_reverse___redArg(v___x_2412_);
v___x_2414_ = lean_array_get_size(v_chain_2413_);
v___x_2415_ = lean_nat_sub(v_chainSizeBeforePrefixTrim_2380_, v___x_2414_);
v___x_2416_ = lean_nat_mod(v___x_2415_, v___x_2382_);
lean_dec(v___x_2415_);
v___x_2417_ = lean_nat_dec_eq(v___x_2416_, v___x_2384_);
lean_dec(v___x_2416_);
if (v___x_2417_ == 0)
{
uint8_t v___x_2418_; 
v___x_2418_ = 1;
v___y_2402_ = v_chain_2413_;
v___y_2403_ = v___x_2414_;
v___y_2404_ = v___y_2410_;
v___y_2405_ = v___x_2418_;
goto v___jp_2401_;
}
else
{
uint8_t v___x_2419_; 
v___x_2419_ = 0;
v___y_2402_ = v_chain_2413_;
v___y_2403_ = v___x_2414_;
v___y_2404_ = v___y_2410_;
v___y_2405_ = v___x_2419_;
goto v___jp_2401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize___boxed(lean_object* v_format_2423_, lean_object* v_chain_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2423_, v_chain_2424_);
lean_dec_ref(v_format_2423_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(lean_object* v___x_2426_, lean_object* v_chain_2427_, lean_object* v_inst_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___redArg(v___x_2426_, v_chain_2427_, v_a_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0___boxed(lean_object* v___x_2431_, lean_object* v_chain_2432_, lean_object* v_inst_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__0(v___x_2431_, v_chain_2432_, v_inst_2433_, v_a_2434_);
lean_dec_ref(v_chain_2432_);
lean_dec(v___x_2431_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(lean_object* v___x_2436_, lean_object* v_chain_2437_, lean_object* v_inst_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___redArg(v___x_2436_, v_chain_2437_, v_a_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1___boxed(lean_object* v___x_2441_, lean_object* v_chain_2442_, lean_object* v_inst_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize_spec__1(v___x_2441_, v_chain_2442_, v_inst_2443_, v_a_2444_);
lean_dec_ref(v_chain_2442_);
lean_dec(v___x_2441_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(lean_object* v_chain_2446_, lean_object* v_format_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2480_; 
v_fst_2449_ = lean_ctor_get(v_a_2448_, 0);
v_snd_2450_ = lean_ctor_get(v_a_2448_, 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2448_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2452_ = v_a_2448_;
v_isShared_2453_ = v_isSharedCheck_2480_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snd_2450_);
lean_inc(v_fst_2449_);
lean_dec(v_a_2448_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2480_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; uint8_t v___x_2455_; 
v___x_2454_ = lean_array_get_size(v_chain_2446_);
v___x_2455_ = lean_nat_dec_lt(v_snd_2450_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2457_; 
if (v_isShared_2453_ == 0)
{
v___x_2457_ = v___x_2452_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_fst_2449_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_snd_2450_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___y_2462_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2459_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2460_ = lean_array_get_borrowed(v___x_2459_, v_chain_2446_, v_snd_2450_);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_add(v_snd_2450_, v___x_2475_);
v___x_2477_ = lean_nat_dec_lt(v___x_2476_, v___x_2454_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; 
lean_dec(v___x_2476_);
v___x_2478_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2462_ = v___x_2478_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_array_fget_borrowed(v_chain_2446_, v___x_2476_);
lean_dec(v___x_2476_);
lean_inc(v___x_2479_);
v___y_2462_ = v___x_2479_;
goto v___jp_2461_;
}
v___jp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2463_ = l_Lean_Fmt_TaggedDoc_nested(v___y_2462_);
v___x_2464_ = lean_unsigned_to_nat(2u);
v___x_2465_ = lean_mk_empty_array_with_capacity(v___x_2464_);
lean_inc(v___x_2460_);
v___x_2466_ = lean_array_push(v___x_2465_, v___x_2460_);
v___x_2467_ = lean_array_push(v___x_2466_, v___x_2463_);
v___x_2468_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2447_, v___x_2467_);
lean_dec_ref(v___x_2467_);
v___x_2469_ = lean_array_push(v_fst_2449_, v___x_2468_);
v___x_2470_ = lean_nat_add(v_snd_2450_, v___x_2464_);
lean_dec(v_snd_2450_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2470_);
lean_ctor_set(v___x_2452_, 0, v___x_2469_);
v___x_2472_ = v___x_2452_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
v_a_2448_ = v___x_2472_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg___boxed(lean_object* v_chain_2481_, lean_object* v_format_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2481_, v_format_2482_, v_a_2483_);
lean_dec_ref(v_format_2482_);
lean_dec_ref(v_chain_2481_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(lean_object* v_chain_2485_, lean_object* v_format_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_fst_2488_; lean_object* v_snd_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2519_; 
v_fst_2488_ = lean_ctor_get(v_a_2487_, 0);
v_snd_2489_ = lean_ctor_get(v_a_2487_, 1);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_a_2487_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2491_ = v_a_2487_;
v_isShared_2492_ = v_isSharedCheck_2519_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_snd_2489_);
lean_inc(v_fst_2488_);
lean_dec(v_a_2487_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2519_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = lean_array_get_size(v_chain_2485_);
v___x_2494_ = lean_nat_dec_lt(v_snd_2489_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2496_; 
if (v_isShared_2492_ == 0)
{
v___x_2496_ = v___x_2491_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_fst_2488_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_snd_2489_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___y_2501_; lean_object* v___x_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2498_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2499_ = lean_array_get_borrowed(v___x_2498_, v_chain_2485_, v_snd_2489_);
v___x_2514_ = lean_unsigned_to_nat(1u);
v___x_2515_ = lean_nat_add(v_snd_2489_, v___x_2514_);
v___x_2516_ = lean_nat_dec_lt(v___x_2515_, v___x_2493_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_dec(v___x_2515_);
v___x_2517_ = l_Lean_Fmt_TaggedDoc_empty;
v___y_2501_ = v___x_2517_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_array_fget_borrowed(v_chain_2485_, v___x_2515_);
lean_dec(v___x_2515_);
lean_inc(v___x_2518_);
v___y_2501_ = v___x_2518_;
goto v___jp_2500_;
}
v___jp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
lean_inc(v___x_2499_);
v___x_2502_ = l_Lean_Fmt_TaggedDoc_nested(v___x_2499_);
v___x_2503_ = lean_unsigned_to_nat(2u);
v___x_2504_ = lean_mk_empty_array_with_capacity(v___x_2503_);
v___x_2505_ = lean_array_push(v___x_2504_, v___x_2502_);
v___x_2506_ = lean_array_push(v___x_2505_, v___y_2501_);
v___x_2507_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2486_, v___x_2506_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = lean_array_push(v_fst_2488_, v___x_2507_);
v___x_2509_ = lean_nat_add(v_snd_2489_, v___x_2503_);
lean_dec(v_snd_2489_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v___x_2509_);
lean_ctor_set(v___x_2491_, 0, v___x_2508_);
v___x_2511_ = v___x_2491_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
v_a_2487_ = v___x_2511_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg___boxed(lean_object* v_chain_2520_, lean_object* v_format_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2520_, v_format_2521_, v_a_2522_);
lean_dec_ref(v_format_2521_);
lean_dec_ref(v_chain_2520_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(lean_object* v_format_2524_, lean_object* v_chain_2525_, uint8_t v_isHeadless_2526_){
_start:
{
lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2534_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2544_; lean_object* v___x_2547_; uint8_t v___y_2549_; uint8_t v_trailingOperator_2562_; 
v___x_2547_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_trailingOperator_2562_ = lean_ctor_get_uint8(v_format_2524_, 1);
v___y_2549_ = v_trailingOperator_2562_;
goto v___jp_2548_;
v___jp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_fst_2532_; 
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___y_2528_);
lean_ctor_set(v___x_2530_, 1, v___y_2529_);
v___x_2531_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2525_, v_format_2524_, v___x_2530_);
v_fst_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_fst_2532_);
lean_dec_ref(v___x_2531_);
return v_fst_2532_;
}
v___jp_2533_:
{
if (v_isHeadless_2526_ == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_unsigned_to_nat(0u);
v___y_2528_ = v___y_2534_;
v___y_2529_ = v___x_2535_;
goto v___jp_2527_;
}
else
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_unsigned_to_nat(1u);
v___y_2528_ = v___y_2534_;
v___y_2529_ = v___x_2536_;
goto v___jp_2527_;
}
}
v___jp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_fst_2542_; 
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___y_2538_);
lean_ctor_set(v___x_2540_, 1, v___y_2539_);
v___x_2541_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2525_, v_format_2524_, v___x_2540_);
v_fst_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_fst_2542_);
lean_dec_ref(v___x_2541_);
return v_fst_2542_;
}
v___jp_2543_:
{
if (v_isHeadless_2526_ == 0)
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_unsigned_to_nat(1u);
v___y_2538_ = v___y_2544_;
v___y_2539_ = v___x_2545_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_unsigned_to_nat(0u);
v___y_2538_ = v___y_2544_;
v___y_2539_ = v___x_2546_;
goto v___jp_2537_;
}
}
v___jp_2548_:
{
if (v___y_2549_ == 0)
{
if (v_isHeadless_2526_ == 0)
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2550_ = lean_unsigned_to_nat(0u);
v___x_2551_ = lean_array_get_borrowed(v___x_2547_, v_chain_2525_, v___x_2550_);
v___x_2552_ = lean_unsigned_to_nat(1u);
v___x_2553_ = lean_mk_empty_array_with_capacity(v___x_2552_);
lean_inc(v___x_2551_);
v___x_2554_ = lean_array_push(v___x_2553_, v___x_2551_);
v___y_2544_ = v___x_2554_;
goto v___jp_2543_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2544_ = v___x_2555_;
goto v___jp_2543_;
}
}
else
{
if (v_isHeadless_2526_ == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___y_2534_ = v___x_2556_;
goto v___jp_2533_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = lean_array_get_borrowed(v___x_2547_, v_chain_2525_, v___x_2557_);
v___x_2559_ = lean_unsigned_to_nat(1u);
v___x_2560_ = lean_mk_empty_array_with_capacity(v___x_2559_);
lean_inc(v___x_2558_);
v___x_2561_ = lean_array_push(v___x_2560_, v___x_2558_);
v___y_2534_ = v___x_2561_;
goto v___jp_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain___boxed(lean_object* v_format_2563_, lean_object* v_chain_2564_, lean_object* v_isHeadless_2565_){
_start:
{
uint8_t v_isHeadless_boxed_2566_; lean_object* v_res_2567_; 
v_isHeadless_boxed_2566_ = lean_unbox(v_isHeadless_2565_);
v_res_2567_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2563_, v_chain_2564_, v_isHeadless_boxed_2566_);
lean_dec_ref(v_chain_2564_);
lean_dec_ref(v_format_2563_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(lean_object* v_chain_2568_, lean_object* v_format_2569_, lean_object* v_inst_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___redArg(v_chain_2568_, v_format_2569_, v_a_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0___boxed(lean_object* v_chain_2573_, lean_object* v_format_2574_, lean_object* v_inst_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__0(v_chain_2573_, v_format_2574_, v_inst_2575_, v_a_2576_);
lean_dec_ref(v_format_2574_);
lean_dec_ref(v_chain_2573_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(lean_object* v_chain_2578_, lean_object* v_format_2579_, lean_object* v_inst_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___redArg(v_chain_2578_, v_format_2579_, v_a_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1___boxed(lean_object* v_chain_2583_, lean_object* v_format_2584_, lean_object* v_inst_2585_, lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain_spec__1(v_chain_2583_, v_format_2584_, v_inst_2585_, v_a_2586_);
lean_dec_ref(v_format_2584_);
lean_dec_ref(v_chain_2583_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(lean_object* v_format_2588_, lean_object* v_docs_2589_){
_start:
{
uint8_t v___y_2591_; uint8_t v___x_2594_; 
v___x_2594_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_alignedOperators(v_format_2588_);
if (v___x_2594_ == 0)
{
uint8_t v___x_2595_; 
v___x_2595_ = l_Lean_Fmt_Layouts_Types_InfixOperatorFormat_separateFinalOperand(v_format_2588_);
if (v___x_2595_ == 0)
{
uint8_t v_spacing_2596_; 
v_spacing_2596_ = lean_ctor_get_uint8(v_format_2588_, 2);
v___y_2591_ = v_spacing_2596_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2597_; uint8_t v___y_2599_; uint8_t v_spacing_2626_; 
v___x_2597_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_spacing_2626_ = lean_ctor_get_uint8(v_format_2588_, 2);
v___y_2599_ = v_spacing_2626_;
goto v___jp_2598_;
v___jp_2598_:
{
if (v___y_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2600_ = lean_unsigned_to_nat(0u);
v___x_2601_ = lean_array_get_size(v_docs_2589_);
v___x_2602_ = lean_unsigned_to_nat(1u);
v___x_2603_ = lean_nat_sub(v___x_2601_, v___x_2602_);
lean_inc(v___x_2603_);
lean_inc_ref(v_docs_2589_);
v___x_2604_ = l_Array_toSubarray___redArg(v_docs_2589_, v___x_2600_, v___x_2603_);
v___x_2605_ = l_Subarray_copy___redArg(v___x_2604_);
v___x_2606_ = l_Lean_Fmt_TaggedDoc_fill(v___x_2605_);
v___x_2607_ = lean_array_get(v___x_2597_, v_docs_2589_, v___x_2603_);
lean_dec(v___x_2603_);
lean_dec_ref(v_docs_2589_);
v___x_2608_ = lean_unsigned_to_nat(2u);
v___x_2609_ = lean_mk_empty_array_with_capacity(v___x_2608_);
v___x_2610_ = lean_array_push(v___x_2609_, v___x_2606_);
v___x_2611_ = lean_array_push(v___x_2610_, v___x_2607_);
v___x_2612_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2611_, v___y_2599_);
lean_dec_ref(v___x_2611_);
return v___x_2612_;
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_array_get_size(v_docs_2589_);
v___x_2615_ = lean_unsigned_to_nat(1u);
v___x_2616_ = lean_nat_sub(v___x_2614_, v___x_2615_);
lean_inc(v___x_2616_);
lean_inc_ref(v_docs_2589_);
v___x_2617_ = l_Array_toSubarray___redArg(v_docs_2589_, v___x_2613_, v___x_2616_);
v___x_2618_ = l_Subarray_copy___redArg(v___x_2617_);
v___x_2619_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v___x_2618_);
v___x_2620_ = lean_array_get(v___x_2597_, v_docs_2589_, v___x_2616_);
lean_dec(v___x_2616_);
lean_dec_ref(v_docs_2589_);
v___x_2621_ = lean_unsigned_to_nat(2u);
v___x_2622_ = lean_mk_empty_array_with_capacity(v___x_2621_);
v___x_2623_ = lean_array_push(v___x_2622_, v___x_2619_);
v___x_2624_ = lean_array_push(v___x_2623_, v___x_2620_);
v___x_2625_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_2624_, v___x_2595_);
lean_dec_ref(v___x_2624_);
return v___x_2625_;
}
}
}
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = l_Lean_Fmt_Layouts_lines(v_docs_2589_);
lean_dec_ref(v_docs_2589_);
return v___x_2627_;
}
v___jp_2590_:
{
if (v___y_2591_ == 0)
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_Fmt_TaggedDoc_fill(v_docs_2589_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_Fmt_TaggedDoc_fillUsingSpace(v_docs_2589_);
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill___boxed(lean_object* v_format_2628_, lean_object* v_docs_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2628_, v_docs_2629_);
lean_dec_ref(v_format_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(lean_object* v_columnPos_2631_, lean_object* v_indentation_2632_, lean_object* v_nonCumulativeIndentation_2633_){
_start:
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = lean_nat_add(v_indentation_2632_, v_nonCumulativeIndentation_2633_);
v___x_2635_ = lean_nat_dec_le(v_columnPos_2631_, v___x_2634_);
lean_dec(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0___boxed(lean_object* v_columnPos_2636_, lean_object* v_indentation_2637_, lean_object* v_nonCumulativeIndentation_2638_){
_start:
{
uint8_t v_res_2639_; lean_object* v_r_2640_; 
v_res_2639_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion___lam__0(v_columnPos_2636_, v_indentation_2637_, v_nonCumulativeIndentation_2638_);
lean_dec(v_nonCumulativeIndentation_2638_);
lean_dec(v_indentation_2637_);
lean_dec(v_columnPos_2636_);
v_r_2640_ = lean_box(v_res_2639_);
return v_r_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(lean_object* v_format_2657_, lean_object* v_combinedChain_2658_){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_firstOperand_2661_; lean_object* v___y_2663_; uint8_t v___y_2684_; uint8_t v_hardNestedFirstOperand_2691_; 
v___x_2659_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2660_ = lean_unsigned_to_nat(0u);
v_firstOperand_2661_ = lean_array_get_borrowed(v___x_2659_, v_combinedChain_2658_, v___x_2660_);
v_hardNestedFirstOperand_2691_ = lean_ctor_get_uint8(v_format_2657_, 0);
v___y_2684_ = v_hardNestedFirstOperand_2691_;
goto v___jp_2683_;
v___jp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v_compactFirstOperation_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v_compactedChain_2678_; lean_object* v___x_2679_; 
lean_inc(v_firstOperand_2661_);
v___x_2664_ = l_Lean_Fmt_TaggedDoc_flattened(v_firstOperand_2661_);
v___x_2665_ = ((lean_object*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperationAssertion));
v___x_2666_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_2665_, v___y_2663_);
v___x_2667_ = lean_unsigned_to_nat(2u);
v___x_2668_ = lean_mk_empty_array_with_capacity(v___x_2667_);
v___x_2669_ = lean_array_push(v___x_2668_, v___x_2664_);
v___x_2670_ = lean_array_push(v___x_2669_, v___x_2666_);
v_compactFirstOperation_2671_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineFlat(v_format_2657_, v___x_2670_);
lean_dec_ref(v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_mk_empty_array_with_capacity(v___x_2672_);
v___x_2674_ = lean_array_push(v___x_2673_, v_compactFirstOperation_2671_);
v___x_2675_ = lean_array_get_size(v_combinedChain_2658_);
v___x_2676_ = l_Array_toSubarray___redArg(v_combinedChain_2658_, v___x_2667_, v___x_2675_);
v___x_2677_ = l_Subarray_copy___redArg(v___x_2676_);
v_compactedChain_2678_ = l_Array_append___redArg(v___x_2674_, v___x_2677_);
lean_dec_ref(v___x_2677_);
v___x_2679_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2657_, v_compactedChain_2678_);
return v___x_2679_;
}
v___jp_2680_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_2682_ = lean_array_get_borrowed(v___x_2659_, v_combinedChain_2658_, v___x_2681_);
lean_inc(v___x_2682_);
v___y_2663_ = v___x_2682_;
goto v___jp_2662_;
}
v___jp_2683_:
{
if (v___y_2684_ == 0)
{
goto v___jp_2680_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_unsigned_to_nat(2u);
v___x_2686_ = lean_array_get_size(v_combinedChain_2658_);
v___x_2687_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
goto v___jp_2680_;
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = lean_array_get_borrowed(v___x_2659_, v_combinedChain_2658_, v___x_2688_);
lean_inc(v___x_2689_);
v___x_2690_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_2689_);
v___y_2663_ = v___x_2690_;
goto v___jp_2662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation___boxed(lean_object* v_format_2692_, lean_object* v_combinedChain_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2692_, v_combinedChain_2693_);
lean_dec_ref(v_format_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(lean_object* v_format_2695_, lean_object* v_docs_2696_, lean_object* v_wrap_2697_){
_start:
{
uint8_t v___y_2699_; uint8_t v_spacing_2702_; 
v_spacing_2702_ = lean_ctor_get_uint8(v_format_2695_, 2);
v___y_2699_ = v_spacing_2702_;
goto v___jp_2698_;
v___jp_2698_:
{
if (v___y_2699_ == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_Fmt_TaggedDoc_fillWrapping(v_docs_2696_, v_wrap_2697_);
return v___x_2700_;
}
else
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWrapping(v_docs_2696_, v_wrap_2697_);
return v___x_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping___boxed(lean_object* v_format_2703_, lean_object* v_docs_2704_, lean_object* v_wrap_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2703_, v_docs_2704_, v_wrap_2705_);
lean_dec_ref(v_format_2703_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(lean_object* v___x_2707_, size_t v_sz_2708_, size_t v_i_2709_, lean_object* v_bs_2710_){
_start:
{
uint8_t v___x_2711_; 
v___x_2711_ = lean_usize_dec_lt(v_i_2709_, v_sz_2708_);
if (v___x_2711_ == 0)
{
return v_bs_2710_;
}
else
{
lean_object* v___x_2712_; lean_object* v_v_2713_; lean_object* v___x_2714_; lean_object* v_bs_x27_2715_; lean_object* v___y_2717_; lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2712_ = lean_unsigned_to_nat(1u);
v_v_2713_ = lean_array_uget(v_bs_2710_, v_i_2709_);
v___x_2714_ = lean_unsigned_to_nat(0u);
v_bs_x27_2715_ = lean_array_uset(v_bs_2710_, v_i_2709_, v___x_2714_);
v___x_2722_ = lean_usize_to_nat(v_i_2709_);
v___x_2723_ = lean_nat_sub(v___x_2707_, v___x_2712_);
v___x_2724_ = lean_nat_dec_lt(v___x_2722_, v___x_2723_);
lean_dec(v___x_2723_);
lean_dec(v___x_2722_);
if (v___x_2724_ == 0)
{
v___y_2717_ = v_v_2713_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2713_);
v___y_2717_ = v___x_2725_;
goto v___jp_2716_;
}
v___jp_2716_:
{
size_t v___x_2718_; size_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2718_ = ((size_t)1ULL);
v___x_2719_ = lean_usize_add(v_i_2709_, v___x_2718_);
v___x_2720_ = lean_array_uset(v_bs_x27_2715_, v_i_2709_, v___y_2717_);
v_i_2709_ = v___x_2719_;
v_bs_2710_ = v___x_2720_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg___boxed(lean_object* v___x_2726_, lean_object* v_sz_2727_, lean_object* v_i_2728_, lean_object* v_bs_2729_){
_start:
{
size_t v_sz_boxed_2730_; size_t v_i_boxed_2731_; lean_object* v_res_2732_; 
v_sz_boxed_2730_ = lean_unbox_usize(v_sz_2727_);
lean_dec(v_sz_2727_);
v_i_boxed_2731_ = lean_unbox_usize(v_i_2728_);
lean_dec(v_i_2728_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2726_, v_sz_boxed_2730_, v_i_boxed_2731_, v_bs_2729_);
lean_dec(v___x_2726_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator(lean_object* v_chain_2747_, lean_object* v_format_2748_){
_start:
{
uint8_t v___y_2750_; lean_object* v_doc_2751_; lean_object* v___x_2755_; lean_object* v_snd_2756_; lean_object* v_fst_2757_; lean_object* v_fst_2758_; lean_object* v_snd_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2755_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_normalize(v_format_2748_, v_chain_2747_);
v_snd_2756_ = lean_ctor_get(v___x_2755_, 1);
lean_inc(v_snd_2756_);
v_fst_2757_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_fst_2757_);
lean_dec_ref(v___x_2755_);
v_fst_2758_ = lean_ctor_get(v_snd_2756_, 0);
lean_inc(v_fst_2758_);
v_snd_2759_ = lean_ctor_get(v_snd_2756_, 1);
lean_inc(v_snd_2759_);
lean_dec(v_snd_2756_);
v___x_2760_ = lean_array_get_size(v_fst_2757_);
v___x_2761_ = lean_unsigned_to_nat(0u);
v___x_2762_ = lean_nat_dec_eq(v___x_2760_, v___x_2761_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; uint8_t v___x_2764_; lean_object* v_combinedChain_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___y_2769_; uint8_t v___y_2770_; lean_object* v_doc_2771_; lean_object* v___y_2786_; lean_object* v___y_2787_; uint8_t v___y_2788_; uint8_t v___x_2795_; lean_object* v___y_2797_; uint8_t v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2802_; uint8_t v___y_2803_; lean_object* v___y_2806_; uint8_t v___y_2807_; lean_object* v_combinedChain_2812_; uint8_t v___y_2815_; uint8_t v___y_2822_; uint8_t v___y_2823_; uint8_t v___y_2831_; uint8_t v___y_2834_; 
v___x_2763_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_2764_ = lean_unbox(v_fst_2758_);
v_combinedChain_2765_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_combineChain(v_format_2748_, v_fst_2757_, v___x_2764_);
v___x_2766_ = lean_array_get_size(v_combinedChain_2765_);
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_nat_dec_eq(v___x_2766_, v___x_2767_);
if (v___x_2795_ == 0)
{
uint8_t v_trailingOperator_2835_; 
v_trailingOperator_2835_ = lean_ctor_get_uint8(v_format_2748_, 1);
v___y_2834_ = v_trailingOperator_2835_;
goto v___jp_2833_;
}
else
{
lean_object* v___x_2836_; 
lean_dec(v_snd_2759_);
lean_dec(v_fst_2758_);
lean_dec(v_fst_2757_);
v___x_2836_ = lean_array_get(v___x_2763_, v_combinedChain_2765_, v___x_2761_);
lean_dec_ref(v_combinedChain_2765_);
return v___x_2836_;
}
v___jp_2768_:
{
lean_object* v___x_2772_; lean_object* v_lastOperand_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; 
v___x_2772_ = lean_nat_sub(v___x_2760_, v___x_2767_);
v_lastOperand_2773_ = lean_array_get(v___x_2763_, v_fst_2757_, v___x_2772_);
lean_dec(v___x_2772_);
lean_dec(v_fst_2757_);
v___x_2774_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
v___x_2775_ = lean_unbox(v_snd_2759_);
lean_inc_ref(v___y_2769_);
lean_inc(v_lastOperand_2773_);
lean_inc_ref(v_doc_2771_);
v___x_2776_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2748_, v_doc_2771_, v_lastOperand_2773_, v___x_2775_, v___y_2769_, v___x_2774_);
if (lean_obj_tag(v___x_2776_) == 1)
{
lean_object* v_val_2777_; 
lean_dec(v_lastOperand_2773_);
lean_dec_ref(v_doc_2771_);
lean_dec_ref(v___y_2769_);
lean_dec(v_snd_2759_);
v_val_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_val_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___y_2750_ = v___y_2770_;
v_doc_2751_ = v_val_2777_;
goto v___jp_2749_;
}
else
{
uint8_t v___x_2778_; lean_object* v___x_2779_; 
lean_dec(v___x_2776_);
v___x_2778_ = lean_unbox(v_snd_2759_);
lean_inc_ref(v___y_2769_);
lean_inc(v_lastOperand_2773_);
lean_inc_ref(v_doc_2771_);
v___x_2779_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addDenseAlt_x3f(v_format_2748_, v_doc_2771_, v_lastOperand_2773_, v___x_2778_, v___y_2769_);
if (lean_obj_tag(v___x_2779_) == 1)
{
lean_object* v_val_2780_; 
lean_dec(v_lastOperand_2773_);
lean_dec_ref(v_doc_2771_);
lean_dec_ref(v___y_2769_);
lean_dec(v_snd_2759_);
v_val_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___y_2750_ = v___y_2770_;
v_doc_2751_ = v_val_2780_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; 
lean_dec(v___x_2779_);
v___x_2781_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
v___x_2782_ = lean_unbox(v_snd_2759_);
lean_dec(v_snd_2759_);
lean_inc_ref(v_doc_2771_);
v___x_2783_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f(v_format_2748_, v_doc_2771_, v_lastOperand_2773_, v___x_2782_, v___y_2769_, v___x_2781_);
if (lean_obj_tag(v___x_2783_) == 1)
{
lean_object* v_val_2784_; 
lean_dec_ref(v_doc_2771_);
v_val_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_val_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___y_2750_ = v___y_2770_;
v_doc_2751_ = v_val_2784_;
goto v___jp_2749_;
}
else
{
lean_dec(v___x_2783_);
v___y_2750_ = v___y_2770_;
v_doc_2751_ = v_doc_2771_;
goto v___jp_2749_;
}
}
}
}
v___jp_2785_:
{
if (v___y_2788_ == 0)
{
v___y_2769_ = v___y_2786_;
v___y_2770_ = v___y_2788_;
v_doc_2771_ = v___y_2787_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v_doc_2794_; 
lean_inc_ref(v___y_2786_);
v___x_2789_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_compactFirstOperation(v_format_2748_, v___y_2786_);
v___x_2790_ = lean_unsigned_to_nat(2u);
v___x_2791_ = lean_mk_empty_array_with_capacity(v___x_2790_);
v___x_2792_ = lean_array_push(v___x_2791_, v___x_2789_);
v___x_2793_ = lean_array_push(v___x_2792_, v___y_2787_);
v_doc_2794_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_2793_);
v___y_2769_ = v___y_2786_;
v___y_2770_ = v___y_2788_;
v_doc_2771_ = v_doc_2794_;
goto v___jp_2768_;
}
}
v___jp_2796_:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_unbox(v_fst_2758_);
lean_dec(v_fst_2758_);
if (v___x_2800_ == 0)
{
v___y_2786_ = v___y_2797_;
v___y_2787_ = v___y_2799_;
v___y_2788_ = v___y_2798_;
goto v___jp_2785_;
}
else
{
if (v___x_2795_ == 0)
{
v___y_2769_ = v___y_2797_;
v___y_2770_ = v___y_2798_;
v_doc_2771_ = v___y_2799_;
goto v___jp_2768_;
}
else
{
v___y_2786_ = v___y_2797_;
v___y_2787_ = v___y_2799_;
v___y_2788_ = v___y_2798_;
goto v___jp_2785_;
}
}
}
v___jp_2801_:
{
lean_object* v___x_2804_; 
lean_inc_ref(v___y_2802_);
v___x_2804_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fill(v_format_2748_, v___y_2802_);
v___y_2797_ = v___y_2802_;
v___y_2798_ = v___y_2803_;
v___y_2799_ = v___x_2804_;
goto v___jp_2796_;
}
v___jp_2805_:
{
if (v___y_2807_ == 0)
{
uint8_t v___x_2808_; 
v___x_2808_ = 1;
v___y_2802_ = v___y_2806_;
v___y_2803_ = v___x_2808_;
goto v___jp_2801_;
}
else
{
if (v___x_2795_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
lean_inc_ref(v___y_2806_);
v___x_2810_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_fillWrapping(v_format_2748_, v___y_2806_, v___x_2809_);
v___y_2797_ = v___y_2806_;
v___y_2798_ = v___x_2795_;
v___y_2799_ = v___x_2810_;
goto v___jp_2796_;
}
else
{
v___y_2802_ = v___y_2806_;
v___y_2803_ = v___x_2795_;
goto v___jp_2801_;
}
}
}
v___jp_2811_:
{
uint8_t v_trailingOperator_2813_; 
v_trailingOperator_2813_ = lean_ctor_get_uint8(v_format_2748_, 1);
v___y_2806_ = v_combinedChain_2812_;
v___y_2807_ = v_trailingOperator_2813_;
goto v___jp_2805_;
}
v___jp_2814_:
{
if (v___y_2815_ == 0)
{
v_combinedChain_2812_ = v_combinedChain_2765_;
goto v___jp_2811_;
}
else
{
size_t v_sz_2816_; size_t v___x_2817_; lean_object* v_combinedChain_2818_; 
v_sz_2816_ = lean_array_size(v_combinedChain_2765_);
v___x_2817_ = ((size_t)0ULL);
v_combinedChain_2818_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2766_, v_sz_2816_, v___x_2817_, v_combinedChain_2765_);
v_combinedChain_2812_ = v_combinedChain_2818_;
goto v___jp_2811_;
}
}
v___jp_2819_:
{
uint8_t v_hardNestedFirstOperand_2820_; 
v_hardNestedFirstOperand_2820_ = lean_ctor_get_uint8(v_format_2748_, 0);
v___y_2815_ = v_hardNestedFirstOperand_2820_;
goto v___jp_2814_;
}
v___jp_2821_:
{
if (v___y_2823_ == 0)
{
if (v___y_2822_ == 0)
{
v_combinedChain_2812_ = v_combinedChain_2765_;
goto v___jp_2811_;
}
else
{
goto v___jp_2819_;
}
}
else
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_nat_dec_lt(v___x_2761_, v___x_2766_);
if (v___x_2824_ == 0)
{
v_combinedChain_2812_ = v_combinedChain_2765_;
goto v___jp_2811_;
}
else
{
lean_object* v_v_2825_; lean_object* v___x_2826_; lean_object* v_xs_x27_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_v_2825_ = lean_array_fget(v_combinedChain_2765_, v___x_2761_);
v___x_2826_ = lean_box(0);
v_xs_x27_2827_ = lean_array_fset(v_combinedChain_2765_, v___x_2761_, v___x_2826_);
v___x_2828_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_2825_);
v___x_2829_ = lean_array_fset(v_xs_x27_2827_, v___x_2761_, v___x_2828_);
v_combinedChain_2812_ = v___x_2829_;
goto v___jp_2811_;
}
}
}
v___jp_2830_:
{
uint8_t v_hardNestedFirstOperand_2832_; 
v_hardNestedFirstOperand_2832_ = lean_ctor_get_uint8(v_format_2748_, 0);
v___y_2822_ = v___y_2831_;
v___y_2823_ = v_hardNestedFirstOperand_2832_;
goto v___jp_2821_;
}
v___jp_2833_:
{
if (v___y_2834_ == 0)
{
v___y_2831_ = v___y_2834_;
goto v___jp_2830_;
}
else
{
if (v___x_2795_ == 0)
{
goto v___jp_2819_;
}
else
{
v___y_2831_ = v___y_2834_;
goto v___jp_2830_;
}
}
}
}
else
{
lean_object* v___x_2837_; 
lean_dec(v_snd_2759_);
lean_dec(v_fst_2758_);
lean_dec(v_fst_2757_);
v___x_2837_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_2837_;
}
v___jp_2749_:
{
if (v___y_2750_ == 0)
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2751_);
return v___x_2752_;
}
else
{
lean_object* v_doc_2753_; lean_object* v___x_2754_; 
v_doc_2753_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2751_);
v___x_2754_ = l_Lean_Fmt_TaggedDoc_nested(v_doc_2753_);
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_infixOperator___boxed(lean_object* v_chain_2838_, lean_object* v_format_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_2838_, v_format_2839_);
lean_dec_ref(v_format_2839_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(lean_object* v___x_2841_, lean_object* v_as_2842_, size_t v_sz_2843_, size_t v_i_2844_, lean_object* v_bs_2845_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___redArg(v___x_2841_, v_sz_2843_, v_i_2844_, v_bs_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0___boxed(lean_object* v___x_2847_, lean_object* v_as_2848_, lean_object* v_sz_2849_, lean_object* v_i_2850_, lean_object* v_bs_2851_){
_start:
{
size_t v_sz_boxed_2852_; size_t v_i_boxed_2853_; lean_object* v_res_2854_; 
v_sz_boxed_2852_ = lean_unbox_usize(v_sz_2849_);
lean_dec(v_sz_2849_);
v_i_boxed_2853_ = lean_unbox_usize(v_i_2850_);
lean_dec(v_i_2850_);
v_res_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_infixOperator_spec__0(v___x_2847_, v_as_2848_, v_sz_boxed_2852_, v_i_boxed_2853_, v_bs_2851_);
lean_dec_ref(v_as_2848_);
lean_dec(v___x_2847_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription(lean_object* v_lhs_2855_, lean_object* v_typeAscriptionTk_2856_, lean_object* v_rhs_2857_, lean_object* v_format_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2859_ = lean_unsigned_to_nat(3u);
v___x_2860_ = lean_mk_empty_array_with_capacity(v___x_2859_);
v___x_2861_ = lean_array_push(v___x_2860_, v_lhs_2855_);
v___x_2862_ = lean_array_push(v___x_2861_, v_typeAscriptionTk_2856_);
v___x_2863_ = lean_array_push(v___x_2862_, v_rhs_2857_);
v___x_2864_ = l_Lean_Fmt_Layouts_infixOperator(v___x_2863_, v_format_2858_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_typeAscription___boxed(lean_object* v_lhs_2865_, lean_object* v_typeAscriptionTk_2866_, lean_object* v_rhs_2867_, lean_object* v_format_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Fmt_Layouts_typeAscription(v_lhs_2865_, v_typeAscriptionTk_2866_, v_rhs_2867_, v_format_2868_);
lean_dec_ref(v_format_2868_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(lean_object* v_x_2870_){
_start:
{
if (lean_obj_tag(v_x_2870_) == 0)
{
lean_object* v___x_2871_; 
v___x_2871_ = lean_unsigned_to_nat(0u);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; 
v___x_2872_ = lean_unsigned_to_nat(1u);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx___boxed(lean_object* v_x_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorIdx(v_x_2873_);
lean_dec_ref(v_x_2873_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(lean_object* v_t_2875_, lean_object* v_k_2876_){
_start:
{
if (lean_obj_tag(v_t_2875_) == 0)
{
uint8_t v_spacing_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
v_spacing_2877_ = lean_ctor_get_uint8(v_t_2875_, 0);
lean_dec_ref_known(v_t_2875_, 0);
v___x_2878_ = lean_box(v_spacing_2877_);
v___x_2879_ = lean_apply_1(v_k_2876_, v___x_2878_);
return v___x_2879_;
}
else
{
lean_object* v_sep_2880_; uint8_t v_unindentedRb_2881_; uint8_t v_stickynessKind_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_sep_2880_ = lean_ctor_get(v_t_2875_, 0);
lean_inc_ref(v_sep_2880_);
v_unindentedRb_2881_ = lean_ctor_get_uint8(v_t_2875_, sizeof(void*)*1);
v_stickynessKind_2882_ = lean_ctor_get_uint8(v_t_2875_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_t_2875_, 1);
v___x_2883_ = lean_box(v_unindentedRb_2881_);
v___x_2884_ = lean_box(v_stickynessKind_2882_);
v___x_2885_ = lean_apply_3(v_k_2876_, v_sep_2880_, v___x_2883_, v___x_2884_);
return v___x_2885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(lean_object* v_motive_2886_, lean_object* v_ctorIdx_2887_, lean_object* v_t_2888_, lean_object* v_h_2889_, lean_object* v_k_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2888_, v_k_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___boxed(lean_object* v_motive_2892_, lean_object* v_ctorIdx_2893_, lean_object* v_t_2894_, lean_object* v_h_2895_, lean_object* v_k_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim(v_motive_2892_, v_ctorIdx_2893_, v_t_2894_, v_h_2895_, v_k_2896_);
lean_dec(v_ctorIdx_2893_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim___redArg(lean_object* v_t_2898_, lean_object* v_dense_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2898_, v_dense_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_dense_elim(lean_object* v_motive_2901_, lean_object* v_t_2902_, lean_object* v_h_2903_, lean_object* v_dense_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2902_, v_dense_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim___redArg(lean_object* v_t_2906_, lean_object* v_sparse_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2906_, v_sparse_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_BracketFormat_sparse_elim(lean_object* v_motive_2909_, lean_object* v_t_2910_, lean_object* v_h_2911_, lean_object* v_sparse_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Fmt_Layouts_Types_BracketFormat_ctorElim___redArg(v_t_2910_, v_sparse_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0(lean_object* v_lb_2914_, lean_object* v_rb_2915_, uint8_t v_isBodyAligned_2916_, uint8_t v_isBodyPseudoAligned_2917_, uint8_t v___x_2918_, lean_object* v_body_2919_){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v_doc_2926_; 
v___x_2920_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2919_);
v___x_2921_ = lean_unsigned_to_nat(3u);
v___x_2922_ = lean_mk_empty_array_with_capacity(v___x_2921_);
v___x_2923_ = lean_array_push(v___x_2922_, v_lb_2914_);
v___x_2924_ = lean_array_push(v___x_2923_, v___x_2920_);
v___x_2925_ = lean_array_push(v___x_2924_, v_rb_2915_);
v_doc_2926_ = l_Lean_Fmt_Layouts_atomic(v___x_2925_);
lean_dec_ref(v___x_2925_);
if (v_isBodyAligned_2916_ == 0)
{
if (v_isBodyPseudoAligned_2917_ == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2926_, v___x_2918_);
return v___x_2927_;
}
else
{
lean_object* v_doc_2928_; lean_object* v___x_2929_; 
v_doc_2928_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v_doc_2926_);
v___x_2929_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2928_, v___x_2918_);
return v___x_2929_;
}
}
else
{
lean_object* v_doc_2930_; lean_object* v___x_2931_; 
v_doc_2930_ = l_Lean_Fmt_TaggedDoc_aligned(v_doc_2926_);
v___x_2931_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v_doc_2930_, v___x_2918_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__0___boxed(lean_object* v_lb_2932_, lean_object* v_rb_2933_, lean_object* v_isBodyAligned_2934_, lean_object* v_isBodyPseudoAligned_2935_, lean_object* v___x_2936_, lean_object* v_body_2937_){
_start:
{
uint8_t v_isBodyAligned_boxed_2938_; uint8_t v_isBodyPseudoAligned_boxed_2939_; uint8_t v___x_641__boxed_2940_; lean_object* v_res_2941_; 
v_isBodyAligned_boxed_2938_ = lean_unbox(v_isBodyAligned_2934_);
v_isBodyPseudoAligned_boxed_2939_ = lean_unbox(v_isBodyPseudoAligned_2935_);
v___x_641__boxed_2940_ = lean_unbox(v___x_2936_);
v_res_2941_ = l_Lean_Fmt_Layouts_bracketed___lam__0(v_lb_2932_, v_rb_2933_, v_isBodyAligned_boxed_2938_, v_isBodyPseudoAligned_boxed_2939_, v___x_641__boxed_2940_, v_body_2937_);
return v_res_2941_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_bracketed___lam__1(uint8_t v_unindentedRb_2942_, lean_object* v_columnPos_2943_, lean_object* v_indentation_2944_, lean_object* v_nonCumulativeIndentation_2945_){
_start:
{
if (v_unindentedRb_2942_ == 0)
{
lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2946_ = lean_nat_add(v_indentation_2944_, v_nonCumulativeIndentation_2945_);
v___x_2947_ = lean_nat_dec_lt(v_columnPos_2943_, v___x_2946_);
lean_dec(v___x_2946_);
return v___x_2947_;
}
else
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_nat_dec_lt(v_columnPos_2943_, v_indentation_2944_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed___lam__1___boxed(lean_object* v_unindentedRb_2949_, lean_object* v_columnPos_2950_, lean_object* v_indentation_2951_, lean_object* v_nonCumulativeIndentation_2952_){
_start:
{
uint8_t v_unindentedRb_662__boxed_2953_; uint8_t v_res_2954_; lean_object* v_r_2955_; 
v_unindentedRb_662__boxed_2953_ = lean_unbox(v_unindentedRb_2949_);
v_res_2954_ = l_Lean_Fmt_Layouts_bracketed___lam__1(v_unindentedRb_662__boxed_2953_, v_columnPos_2950_, v_indentation_2951_, v_nonCumulativeIndentation_2952_);
lean_dec(v_nonCumulativeIndentation_2952_);
lean_dec(v_indentation_2951_);
lean_dec(v_columnPos_2950_);
v_r_2955_ = lean_box(v_res_2954_);
return v_r_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_bracketed(lean_object* v_lb_2965_, lean_object* v_body_2966_, lean_object* v_rb_2967_, lean_object* v_format_2968_){
_start:
{
uint8_t v___x_2969_; 
v___x_2969_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2966_);
if (v___x_2969_ == 0)
{
lean_object* v_doc_2970_; uint8_t v___x_2971_; 
v_doc_2970_ = lean_ctor_get(v_body_2966_, 0);
v___x_2971_ = 1;
if (lean_obj_tag(v_format_2968_) == 0)
{
uint8_t v_spacing_2972_; 
v_spacing_2972_ = lean_ctor_get_uint8(v_format_2968_, 0);
lean_dec_ref_known(v_format_2968_, 0);
if (v_spacing_2972_ == 0)
{
uint8_t v_isBodyAligned_2973_; uint8_t v_isBodyPseudoAligned_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v_f_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_inc(v_doc_2970_);
v_isBodyAligned_2973_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_isAligned___at___00Lean_Fmt_Layouts_prefixOperator_spec__0(v_doc_2970_);
lean_inc_ref(v_body_2966_);
v_isBodyPseudoAligned_2974_ = l_Lean_Fmt_TaggedDoc_isPseudoAligned(v_body_2966_);
v___x_2975_ = lean_box(v_isBodyAligned_2973_);
v___x_2976_ = lean_box(v_isBodyPseudoAligned_2974_);
v___x_2977_ = lean_box(v___x_2971_);
v_f_2978_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__0___boxed), 6, 5);
lean_closure_set(v_f_2978_, 0, v_lb_2965_);
lean_closure_set(v_f_2978_, 1, v_rb_2967_);
lean_closure_set(v_f_2978_, 2, v___x_2975_);
lean_closure_set(v_f_2978_, 3, v___x_2976_);
lean_closure_set(v_f_2978_, 4, v___x_2977_);
v___x_2979_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__0));
v___x_2980_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_body_2966_, v_f_2978_, v___x_2979_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2981_ = l_Lean_Fmt_TaggedDoc_nested(v_body_2966_);
v___x_2982_ = lean_unsigned_to_nat(3u);
v___x_2983_ = lean_mk_empty_array_with_capacity(v___x_2982_);
v___x_2984_ = lean_array_push(v___x_2983_, v_lb_2965_);
v___x_2985_ = lean_array_push(v___x_2984_, v___x_2981_);
v___x_2986_ = lean_array_push(v___x_2985_, v_rb_2967_);
v___x_2987_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_2986_);
lean_dec_ref(v___x_2986_);
return v___x_2987_;
}
}
else
{
lean_object* v_sep_2988_; uint8_t v_unindentedRb_2989_; uint8_t v_stickynessKind_2990_; lean_object* v___x_2991_; lean_object* v_denseAssertion_2992_; lean_object* v_body_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v_dense_3002_; lean_object* v_sparse_3004_; lean_object* v___y_3017_; lean_object* v___y_3020_; lean_object* v___y_3032_; lean_object* v___y_3044_; uint8_t v___x_3056_; 
v_sep_2988_ = lean_ctor_get(v_format_2968_, 0);
lean_inc_ref_n(v_sep_2988_, 2);
v_unindentedRb_2989_ = lean_ctor_get_uint8(v_format_2968_, sizeof(void*)*1);
v_stickynessKind_2990_ = lean_ctor_get_uint8(v_format_2968_, sizeof(void*)*1 + 1);
lean_dec_ref_known(v_format_2968_, 1);
v___x_2991_ = lean_box(v_unindentedRb_2989_);
v_denseAssertion_2992_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_bracketed___lam__1___boxed), 4, 1);
lean_closure_set(v_denseAssertion_2992_, 0, v___x_2991_);
v_body_2993_ = l_Lean_Fmt_TaggedDoc_aligned(v_body_2966_);
v___x_2994_ = l_Lean_Fmt_TaggedDoc_flattened(v_sep_2988_);
v___x_2995_ = lean_unsigned_to_nat(5u);
v___x_2996_ = lean_mk_empty_array_with_capacity(v___x_2995_);
lean_inc_ref(v_lb_2965_);
v___x_2997_ = lean_array_push(v___x_2996_, v_lb_2965_);
lean_inc_ref(v___x_2994_);
v___x_2998_ = lean_array_push(v___x_2997_, v___x_2994_);
lean_inc_ref(v_body_2993_);
v___x_2999_ = lean_array_push(v___x_2998_, v_body_2993_);
v___x_3000_ = lean_array_push(v___x_2999_, v___x_2994_);
lean_inc_ref(v_rb_2967_);
v___x_3001_ = lean_array_push(v___x_3000_, v_rb_2967_);
v_dense_3002_ = l_Lean_Fmt_Layouts_atomic(v___x_3001_);
lean_dec_ref(v___x_3001_);
v___x_3056_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2988_);
if (v___x_3056_ == 0)
{
uint8_t v___x_3057_; 
v___x_3057_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_2993_);
if (v___x_3057_ == 0)
{
lean_object* v_doc_3058_; lean_object* v_doc_3059_; uint8_t v___x_3060_; 
v_doc_3058_ = lean_ctor_get(v_sep_2988_, 0);
v_doc_3059_ = lean_ctor_get(v_body_2993_, 0);
lean_inc(v_doc_3059_);
lean_dec_ref(v_body_2993_);
v___x_3060_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3058_);
if (v___x_3060_ == 0)
{
uint8_t v___x_3061_; 
v___x_3061_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3059_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_inc(v_doc_3058_);
v___x_3062_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_3058_, v_doc_3059_);
v___x_3063_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3062_);
v___y_3044_ = v___x_3063_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3064_; 
lean_dec(v_doc_3059_);
lean_inc(v_doc_3058_);
v___x_3064_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3058_);
v___y_3044_ = v___x_3064_;
goto v___jp_3043_;
}
}
else
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3059_);
v___y_3044_ = v___x_3065_;
goto v___jp_3043_;
}
}
else
{
lean_dec_ref(v_body_2993_);
lean_inc_ref(v_sep_2988_);
v___y_3044_ = v_sep_2988_;
goto v___jp_3043_;
}
}
else
{
v___y_3044_ = v_body_2993_;
goto v___jp_3043_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v_stickyVariant_3013_; lean_object* v_nonStickyVariant_3014_; lean_object* v___x_3015_; 
v___x_3005_ = ((lean_object*)(l_Lean_Fmt_Layouts_bracketed___closed__2));
v___x_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3006_, 0, v_denseAssertion_2992_);
lean_ctor_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = l_Lean_Fmt_TaggedDoc_guarded(v___x_3006_, v_dense_3002_);
v___x_3008_ = lean_unsigned_to_nat(2u);
v___x_3009_ = lean_mk_empty_array_with_capacity(v___x_3008_);
v___x_3010_ = lean_array_push(v___x_3009_, v___x_3007_);
v___x_3011_ = lean_array_push(v___x_3010_, v_sparse_3004_);
v___x_3012_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3011_);
v_stickyVariant_3013_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_3012_, v___x_2971_);
lean_inc_ref(v_stickyVariant_3013_);
v_nonStickyVariant_3014_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_stickyVariant_3013_);
v___x_3015_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyVariant_3014_, v_stickyVariant_3013_, v_stickynessKind_2990_);
return v___x_3015_;
}
v___jp_3016_:
{
if (v_unindentedRb_2989_ == 0)
{
v_sparse_3004_ = v___y_3017_;
goto v___jp_3003_;
}
else
{
lean_object* v_sparse_3018_; 
v_sparse_3018_ = l_Lean_Fmt_TaggedDoc_unindented(v___y_3017_, v___x_2971_);
v_sparse_3004_ = v_sparse_3018_;
goto v___jp_3003_;
}
}
v___jp_3019_:
{
uint8_t v___x_3021_; 
v___x_3021_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_3020_);
if (v___x_3021_ == 0)
{
uint8_t v___x_3022_; 
v___x_3022_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rb_2967_);
if (v___x_3022_ == 0)
{
lean_object* v_doc_3023_; lean_object* v_doc_3024_; uint8_t v___x_3025_; 
v_doc_3023_ = lean_ctor_get(v___y_3020_, 0);
lean_inc(v_doc_3023_);
lean_dec_ref(v___y_3020_);
v_doc_3024_ = lean_ctor_get(v_rb_2967_, 0);
lean_inc(v_doc_3024_);
lean_dec_ref(v_rb_2967_);
v___x_3025_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3023_);
if (v___x_3025_ == 0)
{
uint8_t v___x_3026_; 
v___x_3026_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3024_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_3023_, v_doc_3024_);
v___x_3028_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3027_);
v___y_3017_ = v___x_3028_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3029_; 
lean_dec(v_doc_3024_);
v___x_3029_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3023_);
v___y_3017_ = v___x_3029_;
goto v___jp_3016_;
}
}
else
{
lean_object* v___x_3030_; 
lean_dec(v_doc_3023_);
v___x_3030_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3024_);
v___y_3017_ = v___x_3030_;
goto v___jp_3016_;
}
}
else
{
lean_dec_ref(v_rb_2967_);
v___y_3017_ = v___y_3020_;
goto v___jp_3016_;
}
}
else
{
lean_dec_ref(v___y_3020_);
v___y_3017_ = v_rb_2967_;
goto v___jp_3016_;
}
}
v___jp_3031_:
{
uint8_t v___x_3033_; 
v___x_3033_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___y_3032_);
if (v___x_3033_ == 0)
{
uint8_t v___x_3034_; 
v___x_3034_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_sep_2988_);
if (v___x_3034_ == 0)
{
lean_object* v_doc_3035_; lean_object* v_doc_3036_; uint8_t v___x_3037_; 
v_doc_3035_ = lean_ctor_get(v___y_3032_, 0);
lean_inc(v_doc_3035_);
lean_dec_ref(v___y_3032_);
v_doc_3036_ = lean_ctor_get(v_sep_2988_, 0);
lean_inc(v_doc_3036_);
lean_dec_ref(v_sep_2988_);
v___x_3037_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3035_);
if (v___x_3037_ == 0)
{
uint8_t v___x_3038_; 
v___x_3038_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3036_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_3035_, v_doc_3036_);
v___x_3040_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3039_);
v___y_3020_ = v___x_3040_;
goto v___jp_3019_;
}
else
{
lean_object* v___x_3041_; 
lean_dec(v_doc_3036_);
v___x_3041_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3035_);
v___y_3020_ = v___x_3041_;
goto v___jp_3019_;
}
}
else
{
lean_object* v___x_3042_; 
lean_dec(v_doc_3035_);
v___x_3042_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3036_);
v___y_3020_ = v___x_3042_;
goto v___jp_3019_;
}
}
else
{
lean_dec_ref(v_sep_2988_);
v___y_3020_ = v___y_3032_;
goto v___jp_3019_;
}
}
else
{
lean_dec_ref(v___y_3032_);
v___y_3020_ = v_sep_2988_;
goto v___jp_3019_;
}
}
v___jp_3043_:
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = l_Lean_Fmt_TaggedDoc_hardNested(v___y_3044_);
v___x_3046_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_lb_2965_);
if (v___x_3046_ == 0)
{
uint8_t v___x_3047_; 
v___x_3047_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v___x_3045_);
if (v___x_3047_ == 0)
{
lean_object* v_doc_3048_; lean_object* v_doc_3049_; uint8_t v___x_3050_; 
v_doc_3048_ = lean_ctor_get(v_lb_2965_, 0);
lean_inc(v_doc_3048_);
lean_dec_ref(v_lb_2965_);
v_doc_3049_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_doc_3049_);
lean_dec_ref(v___x_3045_);
v___x_3050_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3048_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
v___x_3051_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_doc_3049_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = l_Lean_Fmt_Doc_append___override___redArg(v_doc_3048_, v_doc_3049_);
v___x_3053_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3052_);
v___y_3032_ = v___x_3053_;
goto v___jp_3031_;
}
else
{
lean_object* v___x_3054_; 
lean_dec(v_doc_3049_);
v___x_3054_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3048_);
v___y_3032_ = v___x_3054_;
goto v___jp_3031_;
}
}
else
{
lean_object* v___x_3055_; 
lean_dec(v_doc_3048_);
v___x_3055_ = l_Lean_Fmt_TaggedDoc_untagged(v_doc_3049_);
v___y_3032_ = v___x_3055_;
goto v___jp_3031_;
}
}
else
{
lean_dec_ref(v___x_3045_);
v___y_3032_ = v_lb_2965_;
goto v___jp_3031_;
}
}
else
{
lean_dec_ref(v_lb_2965_);
v___y_3032_ = v___x_3045_;
goto v___jp_3031_;
}
}
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_dec_ref(v_format_2968_);
lean_dec_ref(v_body_2966_);
v___x_3066_ = lean_unsigned_to_nat(2u);
v___x_3067_ = lean_mk_empty_array_with_capacity(v___x_3066_);
v___x_3068_ = lean_array_push(v___x_3067_, v_lb_2965_);
v___x_3069_ = lean_array_push(v___x_3068_, v_rb_2967_);
v___x_3070_ = l_Lean_Fmt_Layouts_atomic(v___x_3069_);
lean_dec_ref(v___x_3069_);
return v___x_3070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parens(lean_object* v_lbTk_3073_, lean_object* v_body_3074_, lean_object* v_rbTk_3075_){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_3077_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_3073_, v_body_3074_, v_rbTk_3075_, v___x_3076_);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0(void){
_start:
{
uint8_t v___x_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3078_ = 1;
v___x_3079_ = 1;
v___x_3080_ = l_Lean_Fmt_TaggedDoc_break;
v___x_3081_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set_uint8(v___x_3081_, sizeof(void*)*1, v___x_3079_);
lean_ctor_set_uint8(v___x_3081_, sizeof(void*)*1 + 1, v___x_3078_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_parenthesizedSeq(lean_object* v_lbTk_3082_, lean_object* v_seq_3083_, lean_object* v_rbTk_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_obj_once(&l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0, &l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_parenthesizedSeq___closed__0);
v___x_3086_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_3082_, v_seq_3083_, v_rbTk_3084_, v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(uint8_t v_isComplex_3087_, lean_object* v_subAlts_3088_){
_start:
{
if (v_isComplex_3087_ == 0)
{
uint8_t v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = 1;
v___x_3090_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_subAlts_3088_, v___x_3089_);
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_Fmt_Layouts_lines(v_subAlts_3088_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts___boxed(lean_object* v_isComplex_3092_, lean_object* v_subAlts_3093_){
_start:
{
uint8_t v_isComplex_boxed_3094_; lean_object* v_res_3095_; 
v_isComplex_boxed_3094_ = lean_unbox(v_isComplex_3092_);
v_res_3095_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_boxed_3094_, v_subAlts_3093_);
lean_dec_ref(v_subAlts_3093_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(size_t v_sz_3096_, size_t v_i_3097_, lean_object* v_bs_3098_){
_start:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_lt(v_i_3097_, v_sz_3096_);
if (v___x_3099_ == 0)
{
return v_bs_3098_;
}
else
{
lean_object* v_v_3100_; lean_object* v___x_3101_; lean_object* v_bs_x27_3102_; lean_object* v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v_v_3100_ = lean_array_uget(v_bs_3098_, v_i_3097_);
v___x_3101_ = lean_unsigned_to_nat(0u);
v_bs_x27_3102_ = lean_array_uset(v_bs_3098_, v_i_3097_, v___x_3101_);
v___x_3103_ = l_Lean_Fmt_TaggedDoc_nested(v_v_3100_);
v___x_3104_ = ((size_t)1ULL);
v___x_3105_ = lean_usize_add(v_i_3097_, v___x_3104_);
v___x_3106_ = lean_array_uset(v_bs_x27_3102_, v_i_3097_, v___x_3103_);
v_i_3097_ = v___x_3105_;
v_bs_3098_ = v___x_3106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0___boxed(lean_object* v_sz_3108_, lean_object* v_i_3109_, lean_object* v_bs_3110_){
_start:
{
size_t v_sz_boxed_3111_; size_t v_i_boxed_3112_; lean_object* v_res_3113_; 
v_sz_boxed_3111_ = lean_unbox_usize(v_sz_3108_);
lean_dec(v_sz_3108_);
v_i_boxed_3112_ = lean_unbox_usize(v_i_3109_);
lean_dec(v_i_3109_);
v_res_3113_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_boxed_3111_, v_i_boxed_3112_, v_bs_3110_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt(lean_object* v_subAlts_3114_, lean_object* v_arrowTk_3115_, lean_object* v_rhs_3116_, uint8_t v_isComplex_3117_){
_start:
{
uint8_t v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3161_; uint8_t v___x_3178_; 
v___x_3178_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_arrowTk_3115_);
if (v___x_3178_ == 0)
{
v___y_3161_ = v___x_3178_;
goto v___jp_3160_;
}
else
{
uint8_t v___x_3179_; 
v___x_3179_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_rhs_3116_);
v___y_3161_ = v___x_3179_;
goto v___jp_3160_;
}
v___jp_3118_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v_lhs_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v_nonStickyDoc_3137_; lean_object* v_flat_3138_; lean_object* v___x_3139_; 
v___x_3122_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_3117_, v___y_3121_);
lean_dec_ref(v___y_3121_);
v___x_3123_ = lean_unsigned_to_nat(2u);
v___x_3124_ = lean_mk_empty_array_with_capacity(v___x_3123_);
lean_inc_ref_n(v___x_3124_, 2);
v___x_3125_ = lean_array_push(v___x_3124_, v___x_3122_);
v___x_3126_ = lean_array_push(v___x_3125_, v_arrowTk_3115_);
v_lhs_3127_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3126_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_lhs_3127_);
v___x_3129_ = l_Lean_Fmt_TaggedDoc_nl;
lean_inc_ref(v___y_3120_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
lean_ctor_set(v___x_3130_, 1, v___y_3120_);
lean_inc_ref(v___x_3128_);
v___x_3131_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3128_, v___x_3130_);
v___x_3132_ = lean_box(0);
lean_inc_ref(v_rhs_3116_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v_rhs_3116_);
v___x_3134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
lean_ctor_set(v___x_3134_, 2, v___x_3132_);
v___x_3135_ = lean_array_push(v___x_3124_, v___x_3131_);
v___x_3136_ = lean_array_push(v___x_3135_, v___x_3134_);
v_nonStickyDoc_3137_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3136_);
lean_dec_ref(v___x_3136_);
lean_inc_ref(v_nonStickyDoc_3137_);
v_flat_3138_ = l_Lean_Fmt_TaggedDoc_flattened(v_nonStickyDoc_3137_);
v___x_3139_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_rhs_3116_);
if (lean_obj_tag(v___x_3139_) == 1)
{
lean_object* v_val_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3158_; 
v_val_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3158_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_val_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3158_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v_stickyVariant_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v_stickyVariant_3144_ = lean_ctor_get(v_val_3140_, 0);
v___x_3145_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v___y_3120_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v___y_3120_);
v___x_3147_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3128_, v___x_3146_);
lean_inc_ref(v_stickyVariant_3144_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_stickyVariant_3144_);
v___x_3149_ = v___x_3142_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_stickyVariant_3144_);
v___x_3149_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v_stickyDoc_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3132_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
lean_ctor_set(v___x_3150_, 2, v___x_3132_);
v___x_3151_ = lean_array_push(v___x_3124_, v___x_3147_);
v___x_3152_ = lean_array_push(v___x_3151_, v___x_3150_);
v_stickyDoc_3153_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3152_);
lean_dec_ref(v___x_3152_);
v___x_3154_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_3140_, v___y_3119_);
lean_dec(v_val_3140_);
v___x_3155_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_nonStickyDoc_3137_, v_stickyDoc_3153_, v___x_3154_);
lean_dec(v___x_3154_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v_flat_3138_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
return v___x_3156_;
}
}
}
else
{
lean_object* v___x_3159_; 
lean_dec(v___x_3139_);
lean_dec_ref_known(v___x_3128_, 1);
lean_dec_ref(v___x_3124_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_flat_3138_);
lean_ctor_set(v___x_3159_, 1, v_nonStickyDoc_3137_);
return v___x_3159_;
}
}
v___jp_3160_:
{
if (v___y_3161_ == 0)
{
lean_object* v___x_3162_; size_t v_sz_3163_; size_t v___x_3164_; lean_object* v_subAlts_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v___x_3162_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_sz_3163_ = lean_array_size(v_subAlts_3114_);
v___x_3164_ = ((size_t)0ULL);
v_subAlts_3165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alt_spec__0(v_sz_3163_, v___x_3164_, v_subAlts_3114_);
v___x_3166_ = lean_array_get_size(v_subAlts_3165_);
v___x_3167_ = lean_unsigned_to_nat(1u);
v___x_3168_ = lean_nat_sub(v___x_3166_, v___x_3167_);
v___x_3169_ = lean_nat_dec_lt(v___x_3168_, v___x_3166_);
if (v___x_3169_ == 0)
{
lean_dec(v___x_3168_);
v___y_3119_ = v___y_3161_;
v___y_3120_ = v___x_3162_;
v___y_3121_ = v_subAlts_3165_;
goto v___jp_3118_;
}
else
{
lean_object* v_v_3170_; lean_object* v___x_3171_; lean_object* v_xs_x27_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_v_3170_ = lean_array_fget(v_subAlts_3165_, v___x_3168_);
v___x_3171_ = lean_box(0);
v_xs_x27_3172_ = lean_array_fset(v_subAlts_3165_, v___x_3168_, v___x_3171_);
v___x_3173_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3170_);
v___x_3174_ = lean_array_fset(v_xs_x27_3172_, v___x_3168_, v___x_3173_);
lean_dec(v___x_3168_);
v___y_3119_ = v___y_3161_;
v___y_3120_ = v___x_3162_;
v___y_3121_ = v___x_3174_;
goto v___jp_3118_;
}
}
else
{
lean_object* v_subAlts_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec_ref(v_rhs_3116_);
lean_dec_ref(v_arrowTk_3115_);
v_subAlts_3175_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_alt_combineSubAlts(v_isComplex_3117_, v_subAlts_3114_);
lean_dec_ref(v_subAlts_3114_);
lean_inc_ref(v_subAlts_3175_);
v___x_3176_ = l_Lean_Fmt_TaggedDoc_flattened(v_subAlts_3175_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v_subAlts_3175_);
return v___x_3177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alt___boxed(lean_object* v_subAlts_3180_, lean_object* v_arrowTk_3181_, lean_object* v_rhs_3182_, lean_object* v_isComplex_3183_){
_start:
{
uint8_t v_isComplex_boxed_3184_; lean_object* v_res_3185_; 
v_isComplex_boxed_3184_ = lean_unbox(v_isComplex_3183_);
v_res_3185_ = l_Lean_Fmt_Layouts_alt(v_subAlts_3180_, v_arrowTk_3181_, v_rhs_3182_, v_isComplex_boxed_3184_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(size_t v_sz_3186_, size_t v_i_3187_, lean_object* v_bs_3188_){
_start:
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_usize_dec_lt(v_i_3187_, v_sz_3186_);
if (v___x_3189_ == 0)
{
return v_bs_3188_;
}
else
{
lean_object* v_v_3190_; lean_object* v_flat_3191_; lean_object* v___x_3192_; lean_object* v_bs_x27_3193_; size_t v___x_3194_; size_t v___x_3195_; lean_object* v___x_3196_; 
v_v_3190_ = lean_array_uget_borrowed(v_bs_3188_, v_i_3187_);
v_flat_3191_ = lean_ctor_get(v_v_3190_, 0);
lean_inc_ref(v_flat_3191_);
v___x_3192_ = lean_unsigned_to_nat(0u);
v_bs_x27_3193_ = lean_array_uset(v_bs_3188_, v_i_3187_, v___x_3192_);
v___x_3194_ = ((size_t)1ULL);
v___x_3195_ = lean_usize_add(v_i_3187_, v___x_3194_);
v___x_3196_ = lean_array_uset(v_bs_x27_3193_, v_i_3187_, v_flat_3191_);
v_i_3187_ = v___x_3195_;
v_bs_3188_ = v___x_3196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1___boxed(lean_object* v_sz_3198_, lean_object* v_i_3199_, lean_object* v_bs_3200_){
_start:
{
size_t v_sz_boxed_3201_; size_t v_i_boxed_3202_; lean_object* v_res_3203_; 
v_sz_boxed_3201_ = lean_unbox_usize(v_sz_3198_);
lean_dec(v_sz_3198_);
v_i_boxed_3202_ = lean_unbox_usize(v_i_3199_);
lean_dec(v_i_3199_);
v_res_3203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_boxed_3201_, v_i_boxed_3202_, v_bs_3200_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(size_t v_sz_3204_, size_t v_i_3205_, lean_object* v_bs_3206_){
_start:
{
uint8_t v___x_3207_; 
v___x_3207_ = lean_usize_dec_lt(v_i_3205_, v_sz_3204_);
if (v___x_3207_ == 0)
{
return v_bs_3206_;
}
else
{
lean_object* v_v_3208_; lean_object* v_nonFlat_3209_; lean_object* v___x_3210_; lean_object* v_bs_x27_3211_; size_t v___x_3212_; size_t v___x_3213_; lean_object* v___x_3214_; 
v_v_3208_ = lean_array_uget_borrowed(v_bs_3206_, v_i_3205_);
v_nonFlat_3209_ = lean_ctor_get(v_v_3208_, 1);
lean_inc_ref(v_nonFlat_3209_);
v___x_3210_ = lean_unsigned_to_nat(0u);
v_bs_x27_3211_ = lean_array_uset(v_bs_3206_, v_i_3205_, v___x_3210_);
v___x_3212_ = ((size_t)1ULL);
v___x_3213_ = lean_usize_add(v_i_3205_, v___x_3212_);
v___x_3214_ = lean_array_uset(v_bs_x27_3211_, v_i_3205_, v_nonFlat_3209_);
v_i_3205_ = v___x_3213_;
v_bs_3206_ = v___x_3214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0___boxed(lean_object* v_sz_3216_, lean_object* v_i_3217_, lean_object* v_bs_3218_){
_start:
{
size_t v_sz_boxed_3219_; size_t v_i_boxed_3220_; lean_object* v_res_3221_; 
v_sz_boxed_3219_ = lean_unbox_usize(v_sz_3216_);
lean_dec(v_sz_3216_);
v_i_boxed_3220_ = lean_unbox_usize(v_i_3217_);
lean_dec(v_i_3217_);
v_res_3221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_boxed_3219_, v_i_boxed_3220_, v_bs_3218_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts(lean_object* v_alts_3222_, uint8_t v_allowFlattenedAlts_3223_){
_start:
{
size_t v_sz_3224_; size_t v___x_3225_; lean_object* v___x_3226_; lean_object* v_unflattened_3227_; 
v_sz_3224_ = lean_array_size(v_alts_3222_);
v___x_3225_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3222_);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__0(v_sz_3224_, v___x_3225_, v_alts_3222_);
v_unflattened_3227_ = l_Lean_Fmt_Layouts_lines(v___x_3226_);
lean_dec_ref(v___x_3226_);
if (v_allowFlattenedAlts_3223_ == 0)
{
lean_object* v___x_3228_; 
lean_dec_ref(v_alts_3222_);
v___x_3228_ = l_Lean_Fmt_TaggedDoc_withPosition(v_unflattened_3227_);
return v___x_3228_;
}
else
{
lean_object* v___x_3229_; lean_object* v_flattened_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_alts_spec__1(v_sz_3224_, v___x_3225_, v_alts_3222_);
v_flattened_3230_ = l_Lean_Fmt_Layouts_lines(v___x_3229_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = lean_unsigned_to_nat(2u);
v___x_3232_ = lean_mk_empty_array_with_capacity(v___x_3231_);
v___x_3233_ = lean_array_push(v___x_3232_, v_flattened_3230_);
v___x_3234_ = lean_array_push(v___x_3233_, v_unflattened_3227_);
v___x_3235_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3234_);
v___x_3236_ = l_Lean_Fmt_TaggedDoc_withPosition(v___x_3235_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_alts___boxed(lean_object* v_alts_3237_, lean_object* v_allowFlattenedAlts_3238_){
_start:
{
uint8_t v_allowFlattenedAlts_boxed_3239_; lean_object* v_res_3240_; 
v_allowFlattenedAlts_boxed_3239_ = lean_unbox(v_allowFlattenedAlts_3238_);
v_res_3240_ = l_Lean_Fmt_Layouts_alts(v_alts_3237_, v_allowFlattenedAlts_boxed_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(uint8_t v_x_3241_){
_start:
{
if (v_x_3241_ == 0)
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_unsigned_to_nat(0u);
return v___x_3242_;
}
else
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_unsigned_to_nat(1u);
return v___x_3243_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx___boxed(lean_object* v_x_3244_){
_start:
{
uint8_t v_x_boxed_3245_; lean_object* v_res_3246_; 
v_x_boxed_3245_ = lean_unbox(v_x_3244_);
v_res_3246_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorIdx(v_x_boxed_3245_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(lean_object* v_k_3247_){
_start:
{
lean_inc(v_k_3247_);
return v_k_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg___boxed(lean_object* v_k_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___redArg(v_k_3248_);
lean_dec(v_k_3248_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(lean_object* v_motive_3250_, lean_object* v_ctorIdx_3251_, uint8_t v_t_3252_, lean_object* v_h_3253_, lean_object* v_k_3254_){
_start:
{
lean_inc(v_k_3254_);
return v_k_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim___boxed(lean_object* v_motive_3255_, lean_object* v_ctorIdx_3256_, lean_object* v_t_3257_, lean_object* v_h_3258_, lean_object* v_k_3259_){
_start:
{
uint8_t v_t_boxed_3260_; lean_object* v_res_3261_; 
v_t_boxed_3260_ = lean_unbox(v_t_3257_);
v_res_3261_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_ctorElim(v_motive_3255_, v_ctorIdx_3256_, v_t_boxed_3260_, v_h_3258_, v_k_3259_);
lean_dec(v_k_3259_);
lean_dec(v_ctorIdx_3256_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(lean_object* v_sticky_3262_){
_start:
{
lean_inc(v_sticky_3262_);
return v_sticky_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___redArg(v_sticky_3263_);
lean_dec(v_sticky_3263_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(lean_object* v_motive_3265_, uint8_t v_t_3266_, lean_object* v_h_3267_, lean_object* v_sticky_3268_){
_start:
{
lean_inc(v_sticky_3268_);
return v_sticky_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim___boxed(lean_object* v_motive_3269_, lean_object* v_t_3270_, lean_object* v_h_3271_, lean_object* v_sticky_3272_){
_start:
{
uint8_t v_t_boxed_3273_; lean_object* v_res_3274_; 
v_t_boxed_3273_ = lean_unbox(v_t_3270_);
v_res_3274_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_sticky_elim(v_motive_3269_, v_t_boxed_3273_, v_h_3271_, v_sticky_3272_);
lean_dec(v_sticky_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3275_){
_start:
{
lean_inc(v_nonSticky_3275_);
return v_nonSticky_3275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___redArg(v_nonSticky_3276_);
lean_dec(v_nonSticky_3276_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(lean_object* v_motive_3278_, uint8_t v_t_3279_, lean_object* v_h_3280_, lean_object* v_nonSticky_3281_){
_start:
{
lean_inc(v_nonSticky_3281_);
return v_nonSticky_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim___boxed(lean_object* v_motive_3282_, lean_object* v_t_3283_, lean_object* v_h_3284_, lean_object* v_nonSticky_3285_){
_start:
{
uint8_t v_t_boxed_3286_; lean_object* v_res_3287_; 
v_t_boxed_3286_ = lean_unbox(v_t_3283_);
v_res_3287_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSeqFormat_nonSticky_elim(v_motive_3282_, v_t_boxed_3286_, v_h_3284_, v_nonSticky_3285_);
lean_dec(v_nonSticky_3285_);
return v_res_3287_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3289_ = l_Lean_Fmt_TaggedDoc_nl;
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
lean_ctor_set(v___x_3290_, 1, v___x_3288_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq(lean_object* v_keywordTk_3291_, lean_object* v_seq_3292_, uint8_t v_format_3293_){
_start:
{
lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v_doc_3296_; 
v___x_3294_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3295_ = 1;
v_doc_3296_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_keywordTk_3291_, v___x_3294_, v_seq_3292_, v___x_3295_);
if (v_format_3293_ == 0)
{
lean_object* v___x_3297_; uint8_t v___x_3298_; lean_object* v___x_3299_; 
lean_inc_ref(v_doc_3296_);
v___x_3297_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3296_);
v___x_3298_ = 1;
v___x_3299_ = l_Lean_Fmt_TaggedDoc_sticky(v___x_3297_, v_doc_3296_, v___x_3298_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_doc_3296_);
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSeq___boxed(lean_object* v_keywordTk_3301_, lean_object* v_seq_3302_, lean_object* v_format_3303_){
_start:
{
uint8_t v_format_boxed_3304_; lean_object* v_res_3305_; 
v_format_boxed_3304_ = lean_unbox(v_format_3303_);
v_res_3305_ = l_Lean_Fmt_Layouts_keywordPrefixedSeq(v_keywordTk_3301_, v_seq_3302_, v_format_boxed_3304_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(uint8_t v_x_3306_){
_start:
{
if (v_x_3306_ == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_unsigned_to_nat(0u);
return v___x_3307_;
}
else
{
lean_object* v___x_3308_; 
v___x_3308_ = lean_unsigned_to_nat(1u);
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx___boxed(lean_object* v_x_3309_){
_start:
{
uint8_t v_x_boxed_3310_; lean_object* v_res_3311_; 
v_x_boxed_3310_ = lean_unbox(v_x_3309_);
v_res_3311_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorIdx(v_x_boxed_3310_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(lean_object* v_k_3312_){
_start:
{
lean_inc(v_k_3312_);
return v_k_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg___boxed(lean_object* v_k_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___redArg(v_k_3313_);
lean_dec(v_k_3313_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(lean_object* v_motive_3315_, lean_object* v_ctorIdx_3316_, uint8_t v_t_3317_, lean_object* v_h_3318_, lean_object* v_k_3319_){
_start:
{
lean_inc(v_k_3319_);
return v_k_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim___boxed(lean_object* v_motive_3320_, lean_object* v_ctorIdx_3321_, lean_object* v_t_3322_, lean_object* v_h_3323_, lean_object* v_k_3324_){
_start:
{
uint8_t v_t_boxed_3325_; lean_object* v_res_3326_; 
v_t_boxed_3325_ = lean_unbox(v_t_3322_);
v_res_3326_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_ctorElim(v_motive_3320_, v_ctorIdx_3321_, v_t_boxed_3325_, v_h_3323_, v_k_3324_);
lean_dec(v_k_3324_);
lean_dec(v_ctorIdx_3321_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(lean_object* v_sticky_3327_){
_start:
{
lean_inc(v_sticky_3327_);
return v_sticky_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___redArg(v_sticky_3328_);
lean_dec(v_sticky_3328_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(lean_object* v_motive_3330_, uint8_t v_t_3331_, lean_object* v_h_3332_, lean_object* v_sticky_3333_){
_start:
{
lean_inc(v_sticky_3333_);
return v_sticky_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim___boxed(lean_object* v_motive_3334_, lean_object* v_t_3335_, lean_object* v_h_3336_, lean_object* v_sticky_3337_){
_start:
{
uint8_t v_t_boxed_3338_; lean_object* v_res_3339_; 
v_t_boxed_3338_ = lean_unbox(v_t_3335_);
v_res_3339_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_sticky_elim(v_motive_3334_, v_t_boxed_3338_, v_h_3336_, v_sticky_3337_);
lean_dec(v_sticky_3337_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3340_){
_start:
{
lean_inc(v_nonSticky_3340_);
return v_nonSticky_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___redArg(v_nonSticky_3341_);
lean_dec(v_nonSticky_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(lean_object* v_motive_3343_, uint8_t v_t_3344_, lean_object* v_h_3345_, lean_object* v_nonSticky_3346_){
_start:
{
lean_inc(v_nonSticky_3346_);
return v_nonSticky_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim___boxed(lean_object* v_motive_3347_, lean_object* v_t_3348_, lean_object* v_h_3349_, lean_object* v_nonSticky_3350_){
_start:
{
uint8_t v_t_boxed_3351_; lean_object* v_res_3352_; 
v_t_boxed_3351_ = lean_unbox(v_t_3348_);
v_res_3352_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedTermFormat_nonSticky_elim(v_motive_3347_, v_t_boxed_3351_, v_h_3349_, v_nonSticky_3350_);
lean_dec(v_nonSticky_3350_);
return v_res_3352_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0(void){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3354_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v___x_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm(lean_object* v_keyword_3356_, lean_object* v_term_3357_, uint8_t v_format_3358_){
_start:
{
lean_object* v___y_3360_; uint8_t v___x_3375_; 
v___x_3375_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_term_3357_);
if (v___x_3375_ == 0)
{
uint8_t v___x_3376_; lean_object* v___y_3378_; uint8_t v___x_3391_; 
v___x_3376_ = 1;
lean_inc_ref(v_term_3357_);
v___x_3391_ = l_Lean_Fmt_Layouts_permitDenseLayout(v_term_3357_, v___x_3375_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_inc_ref(v_keyword_3356_);
v___x_3392_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3356_);
v___x_3393_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_term_3357_);
v___x_3394_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3392_, v___x_3393_, v_term_3357_, v___x_3376_);
v___x_3395_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3394_);
v___y_3378_ = v___x_3395_;
goto v___jp_3377_;
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
lean_inc_ref(v_keyword_3356_);
v___x_3396_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3356_);
v___x_3397_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v_term_3357_);
v___x_3398_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3396_, v___x_3397_, v_term_3357_, v___x_3376_);
v___y_3378_ = v___x_3398_;
goto v___jp_3377_;
}
v___jp_3377_:
{
if (v_format_3358_ == 0)
{
lean_object* v___x_3379_; 
lean_inc_ref(v_term_3357_);
v___x_3379_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_term_3357_);
if (lean_obj_tag(v___x_3379_) == 1)
{
lean_object* v_val_3380_; uint8_t v_kind_3381_; 
v_val_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_val_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v_kind_3381_ = lean_ctor_get_uint8(v_val_3380_, sizeof(void*)*1);
lean_dec(v_val_3380_);
if (v_kind_3381_ == 1)
{
v___y_3360_ = v___y_3378_;
goto v___jp_3359_;
}
else
{
if (v___x_3375_ == 0)
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3382_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3356_);
v___x_3383_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3384_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3382_, v___x_3383_, v_term_3357_, v___x_3376_);
v___x_3385_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3378_, v___x_3384_, v_kind_3381_);
return v___x_3385_;
}
else
{
v___y_3360_ = v___y_3378_;
goto v___jp_3359_;
}
}
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; 
lean_dec(v___x_3379_);
v___x_3386_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3356_);
v___x_3387_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3388_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___x_3386_, v___x_3387_, v_term_3357_, v___x_3376_);
v___x_3389_ = 0;
v___x_3390_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3378_, v___x_3388_, v___x_3389_);
return v___x_3390_;
}
}
else
{
lean_dec_ref(v_term_3357_);
lean_dec_ref(v_keyword_3356_);
return v___y_3378_;
}
}
}
else
{
uint8_t v___x_3399_; 
lean_dec_ref(v_term_3357_);
v___x_3399_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keyword_3356_);
if (v___x_3399_ == 0)
{
if (v_format_3358_ == 0)
{
lean_object* v___x_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; 
lean_inc_ref(v_keyword_3356_);
v___x_3400_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3356_);
v___x_3401_ = 0;
v___x_3402_ = l_Lean_Fmt_TaggedDoc_sticky(v_keyword_3356_, v___x_3400_, v___x_3401_);
return v___x_3402_;
}
else
{
return v_keyword_3356_;
}
}
else
{
lean_object* v___x_3403_; 
lean_dec_ref(v_keyword_3356_);
v___x_3403_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3403_;
}
}
v___jp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; 
v___x_3361_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3356_);
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
v___x_3363_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3364_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3362_, v___x_3363_);
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_term_3357_);
v___x_3367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
lean_ctor_set(v___x_3367_, 2, v___x_3365_);
v___x_3368_ = lean_unsigned_to_nat(2u);
v___x_3369_ = lean_mk_empty_array_with_capacity(v___x_3368_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3364_);
v___x_3371_ = lean_array_push(v___x_3370_, v___x_3367_);
v___x_3372_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3371_);
lean_dec_ref(v___x_3371_);
v___x_3373_ = 1;
v___x_3374_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_3360_, v___x_3372_, v___x_3373_);
return v___x_3374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedTerm___boxed(lean_object* v_keyword_3404_, lean_object* v_term_3405_, lean_object* v_format_3406_){
_start:
{
uint8_t v_format_boxed_3407_; lean_object* v_res_3408_; 
v_format_boxed_3407_ = lean_unbox(v_format_3406_);
v_res_3408_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3404_, v_term_3405_, v_format_boxed_3407_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(uint8_t v_x_3409_){
_start:
{
if (v_x_3409_ == 0)
{
lean_object* v___x_3410_; 
v___x_3410_ = lean_unsigned_to_nat(0u);
return v___x_3410_;
}
else
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_unsigned_to_nat(1u);
return v___x_3411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx___boxed(lean_object* v_x_3412_){
_start:
{
uint8_t v_x_boxed_3413_; lean_object* v_res_3414_; 
v_x_boxed_3413_ = lean_unbox(v_x_3412_);
v_res_3414_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorIdx(v_x_boxed_3413_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(lean_object* v_k_3415_){
_start:
{
lean_inc(v_k_3415_);
return v_k_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg___boxed(lean_object* v_k_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___redArg(v_k_3416_);
lean_dec(v_k_3416_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(lean_object* v_motive_3418_, lean_object* v_ctorIdx_3419_, uint8_t v_t_3420_, lean_object* v_h_3421_, lean_object* v_k_3422_){
_start:
{
lean_inc(v_k_3422_);
return v_k_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim___boxed(lean_object* v_motive_3423_, lean_object* v_ctorIdx_3424_, lean_object* v_t_3425_, lean_object* v_h_3426_, lean_object* v_k_3427_){
_start:
{
uint8_t v_t_boxed_3428_; lean_object* v_res_3429_; 
v_t_boxed_3428_ = lean_unbox(v_t_3425_);
v_res_3429_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_ctorElim(v_motive_3423_, v_ctorIdx_3424_, v_t_boxed_3428_, v_h_3426_, v_k_3427_);
lean_dec(v_k_3427_);
lean_dec(v_ctorIdx_3424_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(lean_object* v_sticky_3430_){
_start:
{
lean_inc(v_sticky_3430_);
return v_sticky_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___redArg(v_sticky_3431_);
lean_dec(v_sticky_3431_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(lean_object* v_motive_3433_, uint8_t v_t_3434_, lean_object* v_h_3435_, lean_object* v_sticky_3436_){
_start:
{
lean_inc(v_sticky_3436_);
return v_sticky_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim___boxed(lean_object* v_motive_3437_, lean_object* v_t_3438_, lean_object* v_h_3439_, lean_object* v_sticky_3440_){
_start:
{
uint8_t v_t_boxed_3441_; lean_object* v_res_3442_; 
v_t_boxed_3441_ = lean_unbox(v_t_3438_);
v_res_3442_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_sticky_elim(v_motive_3437_, v_t_boxed_3441_, v_h_3439_, v_sticky_3440_);
lean_dec(v_sticky_3440_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3443_){
_start:
{
lean_inc(v_nonSticky_3443_);
return v_nonSticky_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___redArg(v_nonSticky_3444_);
lean_dec(v_nonSticky_3444_);
return v_res_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(lean_object* v_motive_3446_, uint8_t v_t_3447_, lean_object* v_h_3448_, lean_object* v_nonSticky_3449_){
_start:
{
lean_inc(v_nonSticky_3449_);
return v_nonSticky_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim___boxed(lean_object* v_motive_3450_, lean_object* v_t_3451_, lean_object* v_h_3452_, lean_object* v_nonSticky_3453_){
_start:
{
uint8_t v_t_boxed_3454_; lean_object* v_res_3455_; 
v_t_boxed_3454_ = lean_unbox(v_t_3451_);
v_res_3455_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedAltsFormat_nonSticky_elim(v_motive_3450_, v_t_boxed_3454_, v_h_3452_, v_nonSticky_3453_);
lean_dec(v_nonSticky_3453_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts(lean_object* v_keyword_3456_, lean_object* v_alts_3457_, uint8_t v_format_3458_){
_start:
{
uint8_t v___x_3459_; lean_object* v_alts_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v_nonStickyDoc_3465_; 
v___x_3459_ = 1;
v_alts_3460_ = l_Lean_Fmt_Layouts_alts(v_alts_3457_, v___x_3459_);
v___x_3461_ = lean_unsigned_to_nat(2u);
v___x_3462_ = lean_mk_empty_array_with_capacity(v___x_3461_);
lean_inc_ref(v_keyword_3456_);
lean_inc_ref(v___x_3462_);
v___x_3463_ = lean_array_push(v___x_3462_, v_keyword_3456_);
lean_inc_ref(v_alts_3460_);
v___x_3464_ = lean_array_push(v___x_3463_, v_alts_3460_);
v_nonStickyDoc_3465_ = l_Lean_Fmt_Layouts_lines(v___x_3464_);
lean_dec_ref(v___x_3464_);
if (v_format_3458_ == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v_stickyDoc_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; 
v___x_3466_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3456_);
v___x_3467_ = lean_array_push(v___x_3462_, v___x_3466_);
v___x_3468_ = lean_array_push(v___x_3467_, v_alts_3460_);
v_stickyDoc_3469_ = l_Lean_Fmt_Layouts_lines(v___x_3468_);
lean_dec_ref(v___x_3468_);
v___x_3470_ = 0;
v___x_3471_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3465_, v_stickyDoc_3469_, v___x_3470_);
return v___x_3471_;
}
else
{
lean_dec_ref(v___x_3462_);
lean_dec_ref(v_alts_3460_);
lean_dec_ref(v_keyword_3456_);
return v_nonStickyDoc_3465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedAlts___boxed(lean_object* v_keyword_3472_, lean_object* v_alts_3473_, lean_object* v_format_3474_){
_start:
{
uint8_t v_format_boxed_3475_; lean_object* v_res_3476_; 
v_format_boxed_3475_ = lean_unbox(v_format_3474_);
v_res_3476_ = l_Lean_Fmt_Layouts_keywordPrefixedAlts(v_keyword_3472_, v_alts_3473_, v_format_boxed_3475_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(lean_object* v_x_3477_){
_start:
{
if (lean_obj_tag(v_x_3477_) == 0)
{
lean_object* v___x_3478_; 
v___x_3478_ = lean_unsigned_to_nat(0u);
return v___x_3478_;
}
else
{
lean_object* v___x_3479_; 
v___x_3479_ = lean_unsigned_to_nat(1u);
return v___x_3479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx___boxed(lean_object* v_x_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorIdx(v_x_3480_);
lean_dec_ref(v_x_3480_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(lean_object* v_t_3482_, lean_object* v_k_3483_){
_start:
{
lean_object* v_sepArrayFormat_3484_; lean_object* v___x_3485_; 
v_sepArrayFormat_3484_ = lean_ctor_get(v_t_3482_, 0);
lean_inc_ref(v_sepArrayFormat_3484_);
lean_dec_ref(v_t_3482_);
v___x_3485_ = lean_apply_1(v_k_3483_, v_sepArrayFormat_3484_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(lean_object* v_motive_3486_, lean_object* v_ctorIdx_3487_, lean_object* v_t_3488_, lean_object* v_h_3489_, lean_object* v_k_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3488_, v_k_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___boxed(lean_object* v_motive_3492_, lean_object* v_ctorIdx_3493_, lean_object* v_t_3494_, lean_object* v_h_3495_, lean_object* v_k_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim(v_motive_3492_, v_ctorIdx_3493_, v_t_3494_, v_h_3495_, v_k_3496_);
lean_dec(v_ctorIdx_3493_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim___redArg(lean_object* v_t_3498_, lean_object* v_sticky_3499_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3498_, v_sticky_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sticky_elim(lean_object* v_motive_3501_, lean_object* v_t_3502_, lean_object* v_h_3503_, lean_object* v_sticky_3504_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3502_, v_sticky_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim___redArg(lean_object* v_t_3506_, lean_object* v_nonSticky_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3506_, v_nonSticky_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_nonSticky_elim(lean_object* v_motive_3509_, lean_object* v_t_3510_, lean_object* v_h_3511_, lean_object* v_nonSticky_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_ctorElim___redArg(v_t_3510_, v_nonSticky_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(lean_object* v_x_3514_){
_start:
{
if (lean_obj_tag(v_x_3514_) == 0)
{
uint8_t v___x_3515_; 
v___x_3515_ = 1;
return v___x_3515_;
}
else
{
uint8_t v___x_3516_; 
v___x_3516_ = 0;
return v___x_3516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky___boxed(lean_object* v_x_3517_){
_start:
{
uint8_t v_res_3518_; lean_object* v_r_3519_; 
v_res_3518_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_x_3517_);
lean_dec_ref(v_x_3517_);
v_r_3519_ = lean_box(v_res_3518_);
return v_r_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(lean_object* v_x_3520_){
_start:
{
lean_object* v_sepArrayFormat_3521_; 
v_sepArrayFormat_3521_ = lean_ctor_get(v_x_3520_, 0);
lean_inc_ref(v_sepArrayFormat_3521_);
return v_sepArrayFormat_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat___boxed(lean_object* v_x_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_sepArrayFormat(v_x_3522_);
lean_dec_ref(v_x_3522_);
return v_res_3523_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v___x_3525_ = l_Lean_Fmt_TaggedDoc_hardNl;
v___x_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set(v___x_3526_, 1, v___x_3524_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray(lean_object* v_sep_3527_, lean_object* v_keyword_3528_, lean_object* v_sepArray_3529_, lean_object* v_format_3530_){
_start:
{
lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___x_3569_; lean_object* v___y_3571_; uint8_t v___y_3572_; lean_object* v___y_3577_; uint8_t v___y_3578_; lean_object* v___y_3594_; lean_object* v_sepArrayFormat_3598_; 
v___x_3569_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v_sepArrayFormat_3598_ = lean_ctor_get(v_format_3530_, 0);
lean_inc_ref(v_sepArrayFormat_3598_);
v___y_3594_ = v_sepArrayFormat_3598_;
goto v___jp_3593_;
v___jp_3531_:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v_nonStickyDoc_3558_; uint8_t v___x_3559_; 
lean_inc_ref(v_keyword_3528_);
v___x_3535_ = l_Lean_Fmt_TaggedDoc_hardNested(v_keyword_3528_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___x_3537_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedTerm___closed__0);
lean_inc_ref(v___x_3536_);
v___x_3538_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3536_, v___x_3537_);
v___x_3539_ = lean_box(0);
lean_inc_ref(v___y_3533_);
lean_inc_ref(v_sep_3527_);
v___x_3540_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3527_, v___y_3534_, v___y_3533_);
lean_dec_ref(v___y_3534_);
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
v___x_3542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3539_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
lean_ctor_set(v___x_3542_, 2, v___x_3539_);
v___x_3543_ = lean_unsigned_to_nat(2u);
v___x_3544_ = lean_mk_empty_array_with_capacity(v___x_3543_);
lean_inc_ref_n(v___x_3544_, 3);
v___x_3545_ = lean_array_push(v___x_3544_, v___x_3538_);
v___x_3546_ = lean_array_push(v___x_3545_, v___x_3542_);
v___x_3547_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3546_);
lean_dec_ref(v___x_3546_);
v___x_3548_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_3549_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3536_, v___x_3548_);
v___x_3550_ = l_Lean_Fmt_Layouts_sepArray(v_sep_3527_, v___y_3532_, v___y_3533_);
lean_dec_ref(v___y_3532_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3539_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
lean_ctor_set(v___x_3552_, 2, v___x_3539_);
v___x_3553_ = lean_array_push(v___x_3544_, v___x_3549_);
lean_inc_ref(v___x_3552_);
v___x_3554_ = lean_array_push(v___x_3553_, v___x_3552_);
v___x_3555_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3554_);
lean_dec_ref(v___x_3554_);
v___x_3556_ = lean_array_push(v___x_3544_, v___x_3547_);
v___x_3557_ = lean_array_push(v___x_3556_, v___x_3555_);
v_nonStickyDoc_3558_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3557_);
v___x_3559_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3530_);
lean_dec_ref(v_format_3530_);
if (v___x_3559_ == 0)
{
lean_dec_ref_known(v___x_3552_, 3);
lean_dec_ref(v___x_3544_);
lean_dec_ref(v_keyword_3528_);
return v_nonStickyDoc_3558_;
}
else
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v_stickyDoc_3566_; uint8_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3560_ = l_Lean_Fmt_TaggedDoc_flattened(v_keyword_3528_);
v___x_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
v___x_3562_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_3563_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3561_, v___x_3562_);
v___x_3564_ = lean_array_push(v___x_3544_, v___x_3563_);
v___x_3565_ = lean_array_push(v___x_3564_, v___x_3552_);
v_stickyDoc_3566_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3565_);
lean_dec_ref(v___x_3565_);
v___x_3567_ = 0;
v___x_3568_ = l_Lean_Fmt_TaggedDoc_sticky(v_nonStickyDoc_3558_, v_stickyDoc_3566_, v___x_3567_);
return v___x_3568_;
}
}
v___jp_3570_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = lean_array_get(v___x_3569_, v___y_3571_, v___x_3573_);
lean_dec_ref(v___y_3571_);
v___x_3575_ = l_Lean_Fmt_Layouts_keywordPrefixedTerm(v_keyword_3528_, v___x_3574_, v___y_3572_);
return v___x_3575_;
}
v___jp_3576_:
{
lean_object* v_sepArray_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
lean_inc_ref(v_sep_3527_);
v_sepArray_3579_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_3527_, v_sepArray_3529_, v___y_3578_);
v___x_3580_ = lean_array_get_size(v_sepArray_3579_);
v___x_3581_ = lean_unsigned_to_nat(1u);
v___x_3582_ = lean_nat_dec_eq(v___x_3580_, v___x_3581_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_nat_dec_lt(v___x_3583_, v___x_3580_);
if (v___x_3584_ == 0)
{
lean_inc_ref(v_sepArray_3579_);
v___y_3532_ = v_sepArray_3579_;
v___y_3533_ = v___y_3577_;
v___y_3534_ = v_sepArray_3579_;
goto v___jp_3531_;
}
else
{
lean_object* v_v_3585_; lean_object* v___x_3586_; lean_object* v_xs_x27_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v_v_3585_ = lean_array_fget(v_sepArray_3579_, v___x_3583_);
v___x_3586_ = lean_box(0);
lean_inc_ref(v_sepArray_3579_);
v_xs_x27_3587_ = lean_array_fset(v_sepArray_3579_, v___x_3583_, v___x_3586_);
v___x_3588_ = l_Lean_Fmt_TaggedDoc_flattened(v_v_3585_);
v___x_3589_ = lean_array_fset(v_xs_x27_3587_, v___x_3583_, v___x_3588_);
v___y_3532_ = v_sepArray_3579_;
v___y_3533_ = v___y_3577_;
v___y_3534_ = v___x_3589_;
goto v___jp_3531_;
}
}
else
{
uint8_t v___x_3590_; 
lean_dec_ref(v___y_3577_);
lean_dec_ref(v_sep_3527_);
v___x_3590_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepArrayFormat_isSticky(v_format_3530_);
lean_dec_ref(v_format_3530_);
if (v___x_3590_ == 0)
{
uint8_t v___x_3591_; 
v___x_3591_ = 1;
v___y_3571_ = v_sepArray_3579_;
v___y_3572_ = v___x_3591_;
goto v___jp_3570_;
}
else
{
uint8_t v___x_3592_; 
v___x_3592_ = 0;
v___y_3571_ = v_sepArray_3579_;
v___y_3572_ = v___x_3592_;
goto v___jp_3570_;
}
}
}
v___jp_3593_:
{
switch(lean_obj_tag(v___y_3594_))
{
case 1:
{
uint8_t v_trailingSep_3595_; 
v_trailingSep_3595_ = lean_ctor_get_uint8(v___y_3594_, sizeof(void*)*1 + 1);
v___y_3577_ = v___y_3594_;
v___y_3578_ = v_trailingSep_3595_;
goto v___jp_3576_;
}
case 3:
{
uint8_t v_trailingSep_3596_; 
v_trailingSep_3596_ = lean_ctor_get_uint8(v___y_3594_, sizeof(void*)*1);
v___y_3577_ = v___y_3594_;
v___y_3578_ = v_trailingSep_3596_;
goto v___jp_3576_;
}
default: 
{
uint8_t v_trailingSep_3597_; 
v_trailingSep_3597_ = lean_ctor_get_uint8(v___y_3594_, sizeof(void*)*2);
v___y_3577_ = v___y_3594_;
v___y_3578_ = v_trailingSep_3597_;
goto v___jp_3576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepArray___boxed(lean_object* v_sep_3599_, lean_object* v_keyword_3600_, lean_object* v_sepArray_3601_, lean_object* v_format_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3599_, v_keyword_3600_, v_sepArray_3601_, v_format_3602_);
lean_dec_ref(v_sepArray_3601_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(uint8_t v_x_3604_){
_start:
{
if (v_x_3604_ == 0)
{
lean_object* v___x_3605_; 
v___x_3605_ = lean_unsigned_to_nat(0u);
return v___x_3605_;
}
else
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_unsigned_to_nat(1u);
return v___x_3606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx___boxed(lean_object* v_x_3607_){
_start:
{
uint8_t v_x_boxed_3608_; lean_object* v_res_3609_; 
v_x_boxed_3608_ = lean_unbox(v_x_3607_);
v_res_3609_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorIdx(v_x_boxed_3608_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(lean_object* v_k_3610_){
_start:
{
lean_inc(v_k_3610_);
return v_k_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg___boxed(lean_object* v_k_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___redArg(v_k_3611_);
lean_dec(v_k_3611_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(lean_object* v_motive_3613_, lean_object* v_ctorIdx_3614_, uint8_t v_t_3615_, lean_object* v_h_3616_, lean_object* v_k_3617_){
_start:
{
lean_inc(v_k_3617_);
return v_k_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim___boxed(lean_object* v_motive_3618_, lean_object* v_ctorIdx_3619_, lean_object* v_t_3620_, lean_object* v_h_3621_, lean_object* v_k_3622_){
_start:
{
uint8_t v_t_boxed_3623_; lean_object* v_res_3624_; 
v_t_boxed_3623_ = lean_unbox(v_t_3620_);
v_res_3624_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_ctorElim(v_motive_3618_, v_ctorIdx_3619_, v_t_boxed_3623_, v_h_3621_, v_k_3622_);
lean_dec(v_k_3622_);
lean_dec(v_ctorIdx_3619_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(lean_object* v_sticky_3625_){
_start:
{
lean_inc(v_sticky_3625_);
return v_sticky_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg___boxed(lean_object* v_sticky_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___redArg(v_sticky_3626_);
lean_dec(v_sticky_3626_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(lean_object* v_motive_3628_, uint8_t v_t_3629_, lean_object* v_h_3630_, lean_object* v_sticky_3631_){
_start:
{
lean_inc(v_sticky_3631_);
return v_sticky_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim___boxed(lean_object* v_motive_3632_, lean_object* v_t_3633_, lean_object* v_h_3634_, lean_object* v_sticky_3635_){
_start:
{
uint8_t v_t_boxed_3636_; lean_object* v_res_3637_; 
v_t_boxed_3636_ = lean_unbox(v_t_3633_);
v_res_3637_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_sticky_elim(v_motive_3632_, v_t_boxed_3636_, v_h_3634_, v_sticky_3635_);
lean_dec(v_sticky_3635_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(lean_object* v_nonSticky_3638_){
_start:
{
lean_inc(v_nonSticky_3638_);
return v_nonSticky_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg___boxed(lean_object* v_nonSticky_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___redArg(v_nonSticky_3639_);
lean_dec(v_nonSticky_3639_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(lean_object* v_motive_3641_, uint8_t v_t_3642_, lean_object* v_h_3643_, lean_object* v_nonSticky_3644_){
_start:
{
lean_inc(v_nonSticky_3644_);
return v_nonSticky_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim___boxed(lean_object* v_motive_3645_, lean_object* v_t_3646_, lean_object* v_h_3647_, lean_object* v_nonSticky_3648_){
_start:
{
uint8_t v_t_boxed_3649_; lean_object* v_res_3650_; 
v_t_boxed_3649_ = lean_unbox(v_t_3646_);
v_res_3650_ = l_Lean_Fmt_Layouts_Types_KeywordPrefixedSepFillFormat_nonSticky_elim(v_motive_3645_, v_t_boxed_3649_, v_h_3647_, v_nonSticky_3648_);
lean_dec(v_nonSticky_3648_);
return v_res_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill(lean_object* v_sep_3655_, lean_object* v_keyword_3656_, lean_object* v_sepArray_3657_, uint8_t v_format_3658_){
_start:
{
if (v_format_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__0));
v___x_3660_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3655_, v_keyword_3656_, v_sepArray_3657_, v___x_3659_);
return v___x_3660_;
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordPrefixedSepFill___closed__1));
v___x_3662_ = l_Lean_Fmt_Layouts_keywordPrefixedSepArray(v_sep_3655_, v_keyword_3656_, v_sepArray_3657_, v___x_3661_);
return v___x_3662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedSepFill___boxed(lean_object* v_sep_3663_, lean_object* v_keyword_3664_, lean_object* v_sepArray_3665_, lean_object* v_format_3666_){
_start:
{
uint8_t v_format_boxed_3667_; lean_object* v_res_3668_; 
v_format_boxed_3667_ = lean_unbox(v_format_3666_);
v_res_3668_ = l_Lean_Fmt_Layouts_keywordPrefixedSepFill(v_sep_3663_, v_keyword_3664_, v_sepArray_3665_, v_format_boxed_3667_);
lean_dec_ref(v_sepArray_3665_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(lean_object* v_format_3669_, lean_object* v_a_3670_){
_start:
{
uint8_t v_nestedRhs_3671_; 
v_nestedRhs_3671_ = lean_ctor_get_uint8(v_format_3669_, 1);
if (v_nestedRhs_3671_ == 0)
{
return v_a_3670_;
}
else
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Fmt_TaggedDoc_nested(v_a_3670_);
return v___x_3672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed(lean_object* v_format_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap(v_format_3673_, v_a_3674_);
lean_dec_ref(v_format_3673_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(lean_object* v_format_3676_){
_start:
{
uint8_t v_allowFlattening_3677_; 
v_allowFlattening_3677_ = lean_ctor_get_uint8(v_format_3676_, 0);
if (v_allowFlattening_3677_ == 0)
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_Fmt_TaggedDoc_hardNl;
return v___x_3678_;
}
else
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_Fmt_TaggedDoc_nl;
return v___x_3679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep___boxed(lean_object* v_format_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3680_);
lean_dec_ref(v_format_3680_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(lean_object* v_rhs_3682_, lean_object* v_format_3683_, lean_object* v_lhs_3684_){
_start:
{
uint8_t v_allowFlattening_3685_; 
v_allowFlattening_3685_ = lean_ctor_get_uint8(v_format_3683_, 0);
if (v_allowFlattening_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3686_, 0, v_lhs_3684_);
v___x_3687_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3683_);
v___x_3688_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3688_, 0, v_format_3683_);
v___x_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3687_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
v___x_3690_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3686_, v___x_3689_);
v___x_3691_ = lean_box(0);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v_rhs_3682_);
v___x_3693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3691_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
lean_ctor_set(v___x_3693_, 2, v___x_3691_);
v___x_3694_ = lean_unsigned_to_nat(2u);
v___x_3695_ = lean_mk_empty_array_with_capacity(v___x_3694_);
v___x_3696_ = lean_array_push(v___x_3695_, v___x_3690_);
v___x_3697_ = lean_array_push(v___x_3696_, v___x_3693_);
v___x_3698_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3697_);
lean_dec_ref(v___x_3697_);
return v___x_3698_;
}
else
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3699_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3683_);
v___x_3700_ = lean_alloc_closure((void*)(l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_wrap___boxed), 2, 1);
lean_closure_set(v___x_3700_, 0, v_format_3683_);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_3684_, v___x_3701_, v_rhs_3682_, v_allowFlattening_3685_);
return v___x_3702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0(lean_object* v___y_3703_){
_start:
{
lean_inc_ref(v___y_3703_);
return v___y_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated___lam__0___boxed(lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_Fmt_Layouts_keywordSeparated___lam__0(v___y_3704_);
lean_dec_ref(v___y_3704_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordSeparated(lean_object* v_lhs_3707_, lean_object* v_keywordTk_3708_, lean_object* v_rhs_3709_, lean_object* v_format_3710_){
_start:
{
uint8_t v___x_3711_; 
v___x_3711_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_keywordTk_3708_);
if (v___x_3711_ == 0)
{
lean_object* v___f_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v_trailingKeywordLhs_3718_; lean_object* v___x_3719_; lean_object* v_leadingKeywordRhs_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___f_3712_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3713_ = lean_unsigned_to_nat(2u);
v___x_3714_ = lean_mk_empty_array_with_capacity(v___x_3713_);
lean_inc_ref(v_lhs_3707_);
lean_inc_ref_n(v___x_3714_, 2);
v___x_3715_ = lean_array_push(v___x_3714_, v_lhs_3707_);
lean_inc_ref(v_keywordTk_3708_);
v___x_3716_ = lean_array_push(v___x_3715_, v_keywordTk_3708_);
v___x_3717_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_3716_);
lean_dec_ref(v___x_3716_);
v_trailingKeywordLhs_3718_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3717_);
lean_inc_ref_n(v_format_3710_, 2);
lean_inc_ref(v_rhs_3709_);
v___x_3719_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3709_, v_format_3710_, v_keywordTk_3708_);
v_leadingKeywordRhs_3720_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3719_);
v___x_3721_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3709_, v_format_3710_, v_trailingKeywordLhs_3718_);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v_lhs_3707_);
v___x_3723_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_sep(v_format_3710_);
lean_dec_ref(v_format_3710_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
lean_ctor_set(v___x_3724_, 1, v___f_3712_);
v___x_3725_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_3722_, v___x_3724_);
v___x_3726_ = lean_box(0);
v___x_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3727_, 0, v_leadingKeywordRhs_3720_);
v___x_3728_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
lean_ctor_set(v___x_3728_, 2, v___x_3726_);
v___x_3729_ = lean_array_push(v___x_3714_, v___x_3725_);
v___x_3730_ = lean_array_push(v___x_3729_, v___x_3728_);
v___x_3731_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3730_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = lean_array_push(v___x_3714_, v___x_3721_);
v___x_3733_ = lean_array_push(v___x_3732_, v___x_3731_);
v___x_3734_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3733_);
v___x_3735_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3734_);
return v___x_3735_;
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
lean_dec_ref(v_keywordTk_3708_);
v___x_3736_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_keywordSeparated_attachRhs(v_rhs_3709_, v_format_3710_, v_lhs_3707_);
v___x_3737_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3736_);
return v___x_3737_;
}
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0(void){
_start:
{
lean_object* v___f_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___f_3738_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_3739_ = l_Lean_Fmt_TaggedDoc_space;
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
lean_ctor_set(v___x_3740_, 1, v___f_3738_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(lean_object* v_terms_3741_){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3742_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3743_ = lean_box(0);
v___x_3744_ = l_Lean_Fmt_TaggedDoc_space;
lean_inc_ref(v_terms_3741_);
v___x_3745_ = lean_array_pop(v_terms_3741_);
v___x_3746_ = l_Lean_Fmt_TaggedDoc_joinUsing(v___x_3744_, v___x_3745_);
v___x_3747_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_3746_);
v___x_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3743_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
lean_ctor_set(v___x_3749_, 2, v___x_3743_);
v___x_3750_ = lean_array_get_size(v_terms_3741_);
v___x_3751_ = lean_unsigned_to_nat(1u);
v___x_3752_ = lean_nat_sub(v___x_3750_, v___x_3751_);
v___x_3753_ = lean_array_get(v___x_3742_, v_terms_3741_, v___x_3752_);
lean_dec(v___x_3752_);
lean_dec_ref(v_terms_3741_);
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
v___x_3755_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_3756_ = l_Lean_Fmt_TaggedDoc_Component_withSepBefore(v___x_3754_, v___x_3755_);
v___x_3757_ = lean_unsigned_to_nat(2u);
v___x_3758_ = lean_mk_empty_array_with_capacity(v___x_3757_);
v___x_3759_ = lean_array_push(v___x_3758_, v___x_3749_);
v___x_3760_ = lean_array_push(v___x_3759_, v___x_3756_);
v___x_3761_ = l_Lean_Fmt_TaggedDoc_combine(v___x_3760_);
lean_dec_ref(v___x_3760_);
return v___x_3761_;
}
}
static lean_object* _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3763_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(lean_object* v_app_3764_, lean_object* v_fillableTerms_3765_, lean_object* v_terms_3766_, lean_object* v_eligibleKinds_3767_){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v_allowFill_3774_; 
v___x_3768_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3769_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3770_ = lean_array_get_size(v_fillableTerms_3765_);
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_nat_sub(v___x_3770_, v___x_3771_);
v___x_3773_ = lean_array_get_borrowed(v___x_3769_, v_fillableTerms_3765_, v___x_3772_);
lean_dec(v___x_3772_);
v_allowFill_3774_ = lean_ctor_get_uint8(v___x_3773_, sizeof(void*)*1);
if (v_allowFill_3774_ == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref(v_terms_3766_);
lean_dec_ref(v_app_3764_);
v___x_3775_ = lean_box(0);
return v___x_3775_;
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3776_ = lean_array_get_size(v_terms_3766_);
v___x_3777_ = lean_nat_sub(v___x_3776_, v___x_3771_);
v___x_3778_ = lean_array_get_borrowed(v___x_3768_, v_terms_3766_, v___x_3777_);
lean_inc(v___x_3778_);
v___x_3779_ = l_Lean_Fmt_TaggedDoc_getStickynessKind_x3f(v___x_3778_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v___x_3780_; 
lean_dec(v___x_3777_);
lean_dec_ref(v_terms_3766_);
lean_dec_ref(v_app_3764_);
v___x_3780_ = lean_box(0);
return v___x_3780_;
}
else
{
lean_object* v_val_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3802_; 
v_val_3781_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3783_ = v___x_3779_;
v_isShared_3784_ = v_isSharedCheck_3802_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_val_3781_);
lean_dec(v___x_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3802_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
uint8_t v___x_3785_; uint8_t v___x_3786_; lean_object* v___y_3788_; 
v___x_3785_ = lean_unbox(v_val_3781_);
lean_dec(v_val_3781_);
v___x_3786_ = l_Array_contains___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__0(v_eligibleKinds_3767_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3797_; 
lean_del_object(v___x_3783_);
lean_dec(v___x_3777_);
lean_dec_ref(v_terms_3766_);
lean_dec_ref(v_app_3764_);
v___x_3797_ = lean_box(0);
return v___x_3797_;
}
else
{
lean_object* v___x_3798_; 
lean_inc(v___x_3778_);
v___x_3798_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v___x_3778_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f___closed__3);
v___x_3800_ = l_panic___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_infixOperator_addStickyAlt_x3f_spec__1(v___x_3799_);
v___y_3788_ = v___x_3800_;
goto v___jp_3787_;
}
else
{
lean_object* v_val_3801_; 
v_val_3801_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_val_3801_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3788_ = v_val_3801_;
goto v___jp_3787_;
}
}
v___jp_3787_:
{
lean_object* v_stickyVariant_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
v_stickyVariant_3789_ = lean_ctor_get(v___y_3788_, 0);
lean_inc_ref(v_stickyVariant_3789_);
v___x_3790_ = lean_array_set(v_terms_3766_, v___x_3777_, v_stickyVariant_3789_);
lean_dec(v___x_3777_);
v___x_3791_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v___x_3790_);
v___x_3792_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v___y_3788_, v___x_3786_);
lean_dec_ref(v___y_3788_);
v___x_3793_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v_app_3764_, v___x_3791_, v___x_3792_);
lean_dec(v___x_3792_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3793_);
v___x_3795_ = v___x_3783_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___boxed(lean_object* v_app_3803_, lean_object* v_fillableTerms_3804_, lean_object* v_terms_3805_, lean_object* v_eligibleKinds_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3803_, v_fillableTerms_3804_, v_terms_3805_, v_eligibleKinds_3806_);
lean_dec_ref(v_eligibleKinds_3806_);
lean_dec_ref(v_fillableTerms_3804_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(lean_object* v_format_3808_, lean_object* v_app_3809_, lean_object* v_terms_3810_){
_start:
{
uint8_t v_sparse_3811_; 
v_sparse_3811_ = lean_ctor_get_uint8(v_format_3808_, 1);
if (v_sparse_3811_ == 0)
{
uint8_t v_respectPseudoAlignment_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; uint8_t v___x_3815_; 
v_respectPseudoAlignment_3812_ = lean_ctor_get_uint8(v_format_3808_, 3);
v___x_3813_ = lean_array_get_size(v_terms_3810_);
v___x_3814_ = lean_unsigned_to_nat(2u);
v___x_3815_ = lean_nat_dec_eq(v___x_3813_, v___x_3814_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; 
lean_dec_ref(v_terms_3810_);
lean_dec_ref(v_app_3809_);
v___x_3816_ = lean_box(0);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3817_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_3818_ = lean_unsigned_to_nat(1u);
v___x_3819_ = lean_nat_sub(v___x_3813_, v___x_3818_);
v___x_3820_ = lean_array_get_borrowed(v___x_3817_, v_terms_3810_, v___x_3819_);
lean_dec(v___x_3819_);
lean_inc(v___x_3820_);
v___x_3821_ = l_Lean_Fmt_Layouts_permitDenseLayout(v___x_3820_, v_respectPseudoAlignment_3812_);
if (v___x_3821_ == 0)
{
lean_object* v___x_3822_; 
lean_dec_ref(v_terms_3810_);
lean_dec_ref(v_app_3809_);
v___x_3822_ = lean_box(0);
return v___x_3822_;
}
else
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3823_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense(v_terms_3810_);
v___x_3824_ = lean_mk_empty_array_with_capacity(v___x_3814_);
v___x_3825_ = lean_array_push(v___x_3824_, v___x_3823_);
v___x_3826_ = lean_array_push(v___x_3825_, v_app_3809_);
v___x_3827_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_3826_);
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
return v___x_3828_;
}
}
}
else
{
lean_object* v___x_3829_; 
lean_dec_ref(v_terms_3810_);
lean_dec_ref(v_app_3809_);
v___x_3829_ = lean_box(0);
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f___boxed(lean_object* v_format_3830_, lean_object* v_app_3831_, lean_object* v_terms_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3830_, v_app_3831_, v_terms_3832_);
lean_dec_ref(v_format_3830_);
return v_res_3833_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__0));
v___x_3836_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3835_);
return v___x_3836_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3837_; lean_object* v_lbTk_3838_; 
v___x_3837_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__1);
v_lbTk_3838_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3837_);
return v_lbTk_3838_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__3));
v___x_3841_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3840_);
return v___x_3841_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_3842_; lean_object* v_rbTk_3843_; 
v___x_3842_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__4);
v_rbTk_3843_ = l_Lean_Fmt_TaggedDoc_untagged(v___x_3842_);
return v_rbTk_3843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(lean_object* v_upperBound_3844_, lean_object* v_a_3845_, lean_object* v_b_3846_){
_start:
{
lean_object* v_a_3848_; uint8_t v___x_3852_; 
v___x_3852_ = lean_nat_dec_lt(v_a_3845_, v_upperBound_3844_);
if (v___x_3852_ == 0)
{
lean_dec(v_a_3845_);
return v_b_3846_;
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v_v_3855_; uint8_t v_allowFill_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3868_; 
v___x_3853_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3854_ = lean_array_get(v___x_3853_, v_b_3846_, v_a_3845_);
v_v_3855_ = lean_ctor_get(v___x_3854_, 0);
v_allowFill_3856_ = lean_ctor_get_uint8(v___x_3854_, sizeof(void*)*1);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3858_ = v___x_3854_;
v_isShared_3859_ = v_isSharedCheck_3868_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_v_3855_);
lean_dec(v___x_3854_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3868_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
uint8_t v___x_3860_; 
lean_inc(v_v_3855_);
v___x_3860_ = l_Lean_Fmt_TaggedDoc_needsAppBrackets(v_v_3855_);
if (v___x_3860_ == 0)
{
lean_del_object(v___x_3858_);
lean_dec(v_v_3855_);
v_a_3848_ = v_b_3846_;
goto v___jp_3847_;
}
else
{
lean_object* v_lbTk_3861_; lean_object* v_rbTk_3862_; lean_object* v___x_3863_; lean_object* v___x_3865_; 
v_lbTk_3861_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__2);
v_rbTk_3862_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___closed__5);
v___x_3863_ = l_Lean_Fmt_Layouts_parens(v_lbTk_3861_, v_v_3855_, v_rbTk_3862_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3863_);
v___x_3865_ = v___x_3858_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3863_);
lean_ctor_set_uint8(v_reuseFailAlloc_3867_, sizeof(void*)*1, v_allowFill_3856_);
v___x_3865_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_array_set(v_b_3846_, v_a_3845_, v___x_3865_);
v_a_3848_ = v___x_3866_;
goto v___jp_3847_;
}
}
}
}
v___jp_3847_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = lean_unsigned_to_nat(1u);
v___x_3850_ = lean_nat_add(v_a_3845_, v___x_3849_);
lean_dec(v_a_3845_);
v_a_3845_ = v___x_3850_;
v_b_3846_ = v_a_3848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg___boxed(lean_object* v_upperBound_3869_, lean_object* v_a_3870_, lean_object* v_b_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3869_, v_a_3870_, v_b_3871_);
lean_dec(v_upperBound_3869_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(lean_object* v_as_3873_, size_t v_i_3874_, size_t v_stop_3875_, lean_object* v_b_3876_){
_start:
{
lean_object* v___y_3878_; uint8_t v___x_3882_; 
v___x_3882_ = lean_usize_dec_eq(v_i_3874_, v_stop_3875_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; lean_object* v_v_3884_; uint8_t v___x_3885_; 
v___x_3883_ = lean_array_uget_borrowed(v_as_3873_, v_i_3874_);
v_v_3884_ = lean_ctor_get(v___x_3883_, 0);
v___x_3885_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_v_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; 
lean_inc(v___x_3883_);
v___x_3886_ = lean_array_push(v_b_3876_, v___x_3883_);
v___y_3878_ = v___x_3886_;
goto v___jp_3877_;
}
else
{
v___y_3878_ = v_b_3876_;
goto v___jp_3877_;
}
}
else
{
return v_b_3876_;
}
v___jp_3877_:
{
size_t v___x_3879_; size_t v___x_3880_; 
v___x_3879_ = ((size_t)1ULL);
v___x_3880_ = lean_usize_add(v_i_3874_, v___x_3879_);
v_i_3874_ = v___x_3880_;
v_b_3876_ = v___y_3878_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2___boxed(lean_object* v_as_3887_, lean_object* v_i_3888_, lean_object* v_stop_3889_, lean_object* v_b_3890_){
_start:
{
size_t v_i_boxed_3891_; size_t v_stop_boxed_3892_; lean_object* v_res_3893_; 
v_i_boxed_3891_ = lean_unbox_usize(v_i_3888_);
lean_dec(v_i_3888_);
v_stop_boxed_3892_ = lean_unbox_usize(v_stop_3889_);
lean_dec(v_stop_3889_);
v_res_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_as_3887_, v_i_boxed_3891_, v_stop_boxed_3892_, v_b_3890_);
lean_dec_ref(v_as_3887_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(size_t v_sz_3894_, size_t v_i_3895_, lean_object* v_bs_3896_){
_start:
{
uint8_t v___x_3897_; 
v___x_3897_ = lean_usize_dec_lt(v_i_3895_, v_sz_3894_);
if (v___x_3897_ == 0)
{
return v_bs_3896_;
}
else
{
lean_object* v_v_3898_; lean_object* v_v_3899_; lean_object* v___x_3900_; lean_object* v_bs_x27_3901_; size_t v___x_3902_; size_t v___x_3903_; lean_object* v___x_3904_; 
v_v_3898_ = lean_array_uget_borrowed(v_bs_3896_, v_i_3895_);
v_v_3899_ = lean_ctor_get(v_v_3898_, 0);
lean_inc(v_v_3899_);
v___x_3900_ = lean_unsigned_to_nat(0u);
v_bs_x27_3901_ = lean_array_uset(v_bs_3896_, v_i_3895_, v___x_3900_);
v___x_3902_ = ((size_t)1ULL);
v___x_3903_ = lean_usize_add(v_i_3895_, v___x_3902_);
v___x_3904_ = lean_array_uset(v_bs_x27_3901_, v_i_3895_, v_v_3899_);
v_i_3895_ = v___x_3903_;
v_bs_3896_ = v___x_3904_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0___boxed(lean_object* v_sz_3906_, lean_object* v_i_3907_, lean_object* v_bs_3908_){
_start:
{
size_t v_sz_boxed_3909_; size_t v_i_boxed_3910_; lean_object* v_res_3911_; 
v_sz_boxed_3909_ = lean_unbox_usize(v_sz_3906_);
lean_dec(v_sz_3906_);
v_i_boxed_3910_ = lean_unbox_usize(v_i_3907_);
lean_dec(v_i_3907_);
v_res_3911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_boxed_3909_, v_i_boxed_3910_, v_bs_3908_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled(lean_object* v_terms_3914_, lean_object* v_format_3915_){
_start:
{
lean_object* v_app_3917_; lean_object* v_fillableTerms_3921_; lean_object* v___y_3935_; lean_object* v_fillableTerms_3936_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___y_3944_; lean_object* v___x_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3941_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f___closed__0);
v___x_3942_ = lean_unsigned_to_nat(0u);
v___x_3969_ = lean_array_get_size(v_terms_3914_);
v___x_3970_ = ((lean_object*)(l_Lean_Fmt_Layouts_applicationWithSomeFilled___closed__0));
v___x_3971_ = lean_nat_dec_lt(v___x_3942_, v___x_3969_);
if (v___x_3971_ == 0)
{
v___y_3944_ = v___x_3970_;
goto v___jp_3943_;
}
else
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_nat_dec_le(v___x_3969_, v___x_3969_);
if (v___x_3972_ == 0)
{
if (v___x_3971_ == 0)
{
v___y_3944_ = v___x_3970_;
goto v___jp_3943_;
}
else
{
size_t v___x_3973_; size_t v___x_3974_; lean_object* v___x_3975_; 
v___x_3973_ = ((size_t)0ULL);
v___x_3974_ = lean_usize_of_nat(v___x_3969_);
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3914_, v___x_3973_, v___x_3974_, v___x_3970_);
v___y_3944_ = v___x_3975_;
goto v___jp_3943_;
}
}
else
{
size_t v___x_3976_; size_t v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = ((size_t)0ULL);
v___x_3977_ = lean_usize_of_nat(v___x_3969_);
v___x_3978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__2(v_terms_3914_, v___x_3976_, v___x_3977_, v___x_3970_);
v___y_3944_ = v___x_3978_;
goto v___jp_3943_;
}
}
v___jp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = l_Lean_Fmt_TaggedDoc_nested(v_app_3917_);
v___x_3919_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_3918_);
return v___x_3919_;
}
v___jp_3920_:
{
lean_object* v_app_3922_; size_t v_sz_3923_; size_t v___x_3924_; lean_object* v_terms_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_inc_ref_n(v_fillableTerms_3921_, 2);
v_app_3922_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpace(v_fillableTerms_3921_);
v_sz_3923_ = lean_array_size(v_fillableTerms_3921_);
v___x_3924_ = ((size_t)0ULL);
v_terms_3925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__0(v_sz_3923_, v___x_3924_, v_fillableTerms_3921_);
v___x_3926_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__0));
lean_inc_ref(v_terms_3925_);
lean_inc_ref(v_app_3922_);
v___x_3927_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3922_, v_fillableTerms_3921_, v_terms_3925_, v___x_3926_);
if (lean_obj_tag(v___x_3927_) == 1)
{
lean_object* v_val_3928_; 
lean_dec_ref(v_terms_3925_);
lean_dec_ref(v_app_3922_);
lean_dec_ref(v_fillableTerms_3921_);
v_val_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_val_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v_app_3917_ = v_val_3928_;
goto v___jp_3916_;
}
else
{
lean_object* v___x_3929_; 
lean_dec(v___x_3927_);
lean_inc_ref(v_terms_3925_);
lean_inc_ref(v_app_3922_);
v___x_3929_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addDenseAlt_x3f(v_format_3915_, v_app_3922_, v_terms_3925_);
if (lean_obj_tag(v___x_3929_) == 1)
{
lean_object* v_val_3930_; 
lean_dec_ref(v_terms_3925_);
lean_dec_ref(v_app_3922_);
lean_dec_ref(v_fillableTerms_3921_);
v_val_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_val_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v_app_3917_ = v_val_3930_;
goto v___jp_3916_;
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec(v___x_3929_);
v___x_3931_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__1));
lean_inc_ref(v_app_3922_);
v___x_3932_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_addStickyAlt_x3f(v_app_3922_, v_fillableTerms_3921_, v_terms_3925_, v___x_3931_);
lean_dec_ref(v_fillableTerms_3921_);
if (lean_obj_tag(v___x_3932_) == 1)
{
lean_object* v_val_3933_; 
lean_dec_ref(v_app_3922_);
v_val_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_val_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v_app_3917_ = v_val_3933_;
goto v___jp_3916_;
}
else
{
lean_dec(v___x_3932_);
v_app_3917_ = v_app_3922_;
goto v___jp_3916_;
}
}
}
}
v___jp_3934_:
{
uint8_t v_parenthesize_3937_; 
v_parenthesize_3937_ = lean_ctor_get_uint8(v_format_3915_, 2);
if (v_parenthesize_3937_ == 0)
{
lean_dec(v___y_3935_);
v_fillableTerms_3921_ = v_fillableTerms_3936_;
goto v___jp_3920_;
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3938_ = lean_array_get_size(v_fillableTerms_3936_);
v___x_3939_ = lean_nat_sub(v___x_3938_, v___y_3935_);
v___x_3940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v___x_3939_, v___y_3935_, v_fillableTerms_3936_);
lean_dec(v___x_3939_);
v_fillableTerms_3921_ = v___x_3940_;
goto v___jp_3920_;
}
}
v___jp_3943_:
{
lean_object* v___x_3945_; uint8_t v___x_3946_; 
v___x_3945_ = lean_array_get_size(v___y_3944_);
v___x_3946_ = lean_nat_dec_eq(v___x_3945_, v___x_3942_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = lean_unsigned_to_nat(1u);
v___x_3948_ = lean_nat_dec_eq(v___x_3945_, v___x_3947_);
if (v___x_3948_ == 0)
{
uint8_t v___x_3949_; 
v___x_3949_ = lean_nat_dec_lt(v___x_3947_, v___x_3945_);
if (v___x_3949_ == 0)
{
v___y_3935_ = v___x_3947_;
v_fillableTerms_3936_ = v___y_3944_;
goto v___jp_3934_;
}
else
{
uint8_t v_hardNestedFirstTerm_3950_; 
v_hardNestedFirstTerm_3950_ = lean_ctor_get_uint8(v_format_3915_, 0);
if (v_hardNestedFirstTerm_3950_ == 0)
{
v___y_3935_ = v___x_3947_;
v_fillableTerms_3936_ = v___y_3944_;
goto v___jp_3934_;
}
else
{
uint8_t v___x_3951_; 
v___x_3951_ = lean_nat_dec_lt(v___x_3942_, v___x_3945_);
if (v___x_3951_ == 0)
{
v___y_3935_ = v___x_3947_;
v_fillableTerms_3936_ = v___y_3944_;
goto v___jp_3934_;
}
else
{
lean_object* v_v_3952_; lean_object* v_v_3953_; uint8_t v_allowFill_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3965_; 
v_v_3952_ = lean_array_fget(v___y_3944_, v___x_3942_);
v_v_3953_ = lean_ctor_get(v_v_3952_, 0);
v_allowFill_3954_ = lean_ctor_get_uint8(v_v_3952_, sizeof(void*)*1);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_v_3952_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3956_ = v_v_3952_;
v_isShared_3957_ = v_isSharedCheck_3965_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_v_3953_);
lean_dec(v_v_3952_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3965_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v_xs_x27_3959_; lean_object* v___x_3960_; lean_object* v___x_3962_; 
v___x_3958_ = lean_box(0);
v_xs_x27_3959_ = lean_array_fset(v___y_3944_, v___x_3942_, v___x_3958_);
v___x_3960_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_3953_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3960_);
v___x_3962_ = v___x_3956_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3964_, sizeof(void*)*1, v_allowFill_3954_);
v___x_3962_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_array_fset(v_xs_x27_3959_, v___x_3942_, v___x_3962_);
v___y_3935_ = v___x_3947_;
v_fillableTerms_3936_ = v___x_3963_;
goto v___jp_3934_;
}
}
}
}
}
}
else
{
lean_object* v___x_3966_; lean_object* v_v_3967_; 
v___x_3966_ = lean_array_get(v___x_3941_, v___y_3944_, v___x_3942_);
lean_dec_ref(v___y_3944_);
v_v_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_v_3967_);
lean_dec(v___x_3966_);
return v_v_3967_;
}
}
else
{
lean_object* v___x_3968_; 
lean_dec_ref(v___y_3944_);
v___x_3968_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_3968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_applicationWithSomeFilled___boxed(lean_object* v_terms_3979_, lean_object* v_format_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v_terms_3979_, v_format_3980_);
lean_dec_ref(v_format_3980_);
lean_dec_ref(v_terms_3979_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(lean_object* v_upperBound_3982_, lean_object* v_inst_3983_, lean_object* v_R_3984_, lean_object* v_a_3985_, lean_object* v_b_3986_, lean_object* v_c_3987_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___redArg(v_upperBound_3982_, v_a_3985_, v_b_3986_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1___boxed(lean_object* v_upperBound_3989_, lean_object* v_inst_3990_, lean_object* v_R_3991_, lean_object* v_a_3992_, lean_object* v_b_3993_, lean_object* v_c_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_applicationWithSomeFilled_spec__1(v_upperBound_3989_, v_inst_3990_, v_R_3991_, v_a_3992_, v_b_3993_, v_c_3994_);
lean_dec(v_upperBound_3989_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(size_t v_sz_3996_, size_t v_i_3997_, lean_object* v_bs_3998_){
_start:
{
uint8_t v___x_3999_; 
v___x_3999_ = lean_usize_dec_lt(v_i_3997_, v_sz_3996_);
if (v___x_3999_ == 0)
{
return v_bs_3998_;
}
else
{
lean_object* v_v_4000_; lean_object* v___x_4001_; lean_object* v_bs_x27_4002_; lean_object* v___x_4003_; size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v_v_4000_ = lean_array_uget(v_bs_3998_, v_i_3997_);
v___x_4001_ = lean_unsigned_to_nat(0u);
v_bs_x27_4002_ = lean_array_uset(v_bs_3998_, v_i_3997_, v___x_4001_);
v___x_4003_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4003_, 0, v_v_4000_);
lean_ctor_set_uint8(v___x_4003_, sizeof(void*)*1, v___x_3999_);
v___x_4004_ = ((size_t)1ULL);
v___x_4005_ = lean_usize_add(v_i_3997_, v___x_4004_);
v___x_4006_ = lean_array_uset(v_bs_x27_4002_, v_i_3997_, v___x_4003_);
v_i_3997_ = v___x_4005_;
v_bs_3998_ = v___x_4006_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0___boxed(lean_object* v_sz_4008_, lean_object* v_i_4009_, lean_object* v_bs_4010_){
_start:
{
size_t v_sz_boxed_4011_; size_t v_i_boxed_4012_; lean_object* v_res_4013_; 
v_sz_boxed_4011_ = lean_unbox_usize(v_sz_4008_);
lean_dec(v_sz_4008_);
v_i_boxed_4012_ = lean_unbox_usize(v_i_4009_);
lean_dec(v_i_4009_);
v_res_4013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_boxed_4011_, v_i_boxed_4012_, v_bs_4010_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application(lean_object* v_terms_4014_, lean_object* v_format_4015_){
_start:
{
size_t v_sz_4016_; size_t v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_sz_4016_ = lean_array_size(v_terms_4014_);
v___x_4017_ = ((size_t)0ULL);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_application_spec__0(v_sz_4016_, v___x_4017_, v_terms_4014_);
v___x_4019_ = l_Lean_Fmt_Layouts_applicationWithSomeFilled(v___x_4018_, v_format_4015_);
lean_dec_ref(v___x_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_application___boxed(lean_object* v_terms_4020_, lean_object* v_format_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Fmt_Layouts_application(v_terms_4020_, v_format_4021_);
lean_dec_ref(v_format_4021_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(lean_object* v_f_4023_){
_start:
{
uint8_t v_hardNestedFirstTerm_4024_; uint8_t v_sparse_4025_; uint8_t v_parenthesize_4026_; uint8_t v_respectPseudoAlignment_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
v_hardNestedFirstTerm_4024_ = lean_ctor_get_uint8(v_f_4023_, 0);
v_sparse_4025_ = lean_ctor_get_uint8(v_f_4023_, 1);
v_parenthesize_4026_ = lean_ctor_get_uint8(v_f_4023_, 2);
v_respectPseudoAlignment_4027_ = lean_ctor_get_uint8(v_f_4023_, 3);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_f_4023_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v_f_4023_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v_f_4023_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v_reuseFailAlloc_4033_, 0, v_hardNestedFirstTerm_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4033_, 1, v_sparse_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4033_, 2, v_parenthesize_4026_);
lean_ctor_set_uint8(v_reuseFailAlloc_4033_, 3, v_respectPseudoAlignment_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object* v_terms_4035_, lean_object* v_format_4036_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = l_Lean_Fmt_Layouts_Types_PseudoApplicationFormat_toApplicationFormat(v_format_4036_);
v___x_4038_ = l_Lean_Fmt_Layouts_application(v_terms_4035_, v___x_4037_);
lean_dec_ref(v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(lean_object* v_x_4039_){
_start:
{
if (lean_obj_tag(v_x_4039_) == 0)
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_unsigned_to_nat(0u);
return v___x_4040_;
}
else
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_unsigned_to_nat(1u);
return v___x_4041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx___boxed(lean_object* v_x_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorIdx(v_x_4042_);
lean_dec_ref(v_x_4042_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(lean_object* v_t_4044_, lean_object* v_k_4045_){
_start:
{
lean_object* v_doc_4046_; lean_object* v___x_4047_; 
v_doc_4046_ = lean_ctor_get(v_t_4044_, 0);
lean_inc_ref(v_doc_4046_);
lean_dec_ref(v_t_4044_);
v___x_4047_ = lean_apply_1(v_k_4045_, v_doc_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(lean_object* v_motive_4048_, lean_object* v_ctorIdx_4049_, lean_object* v_t_4050_, lean_object* v_h_4051_, lean_object* v_k_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4050_, v_k_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___boxed(lean_object* v_motive_4054_, lean_object* v_ctorIdx_4055_, lean_object* v_t_4056_, lean_object* v_h_4057_, lean_object* v_k_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim(v_motive_4054_, v_ctorIdx_4055_, v_t_4056_, v_h_4057_, v_k_4058_);
lean_dec(v_ctorIdx_4055_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim___redArg(lean_object* v_t_4060_, lean_object* v_sep_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4060_, v_sep_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_sep_elim(lean_object* v_motive_4063_, lean_object* v_t_4064_, lean_object* v_h_4065_, lean_object* v_sep_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4064_, v_sep_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim___redArg(lean_object* v_t_4068_, lean_object* v_elems_4069_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4068_, v_elems_4069_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_elems_elim(lean_object* v_motive_4071_, lean_object* v_t_4072_, lean_object* v_h_4073_, lean_object* v_elems_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_Fmt_Layouts_metaApplication_Term_ctorElim___redArg(v_t_4072_, v_elems_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(size_t v_sz_4076_, size_t v_i_4077_, lean_object* v_bs_4078_){
_start:
{
uint8_t v___x_4079_; 
v___x_4079_ = lean_usize_dec_lt(v_i_4077_, v_sz_4076_);
if (v___x_4079_ == 0)
{
return v_bs_4078_;
}
else
{
lean_object* v_v_4080_; lean_object* v___x_4081_; lean_object* v_bs_x27_4082_; lean_object* v___y_4084_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; 
v_v_4080_ = lean_array_uget(v_bs_4078_, v_i_4077_);
v___x_4081_ = lean_unsigned_to_nat(0u);
v_bs_x27_4082_ = lean_array_uset(v_bs_4078_, v_i_4077_, v___x_4081_);
v___x_4089_ = lean_usize_to_nat(v_i_4077_);
v___x_4090_ = lean_unsigned_to_nat(2u);
v___x_4091_ = lean_nat_mod(v___x_4089_, v___x_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_nat_dec_eq(v___x_4091_, v___x_4081_);
lean_dec(v___x_4091_);
if (v___x_4092_ == 0)
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_v_4080_);
v___y_4084_ = v___x_4093_;
goto v___jp_4083_;
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4094_ = lean_unsigned_to_nat(1u);
v___x_4095_ = lean_mk_empty_array_with_capacity(v___x_4094_);
v___x_4096_ = lean_array_push(v___x_4095_, v_v_4080_);
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
v___y_4084_ = v___x_4097_;
goto v___jp_4083_;
}
v___jp_4083_:
{
size_t v___x_4085_; size_t v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = ((size_t)1ULL);
v___x_4086_ = lean_usize_add(v_i_4077_, v___x_4085_);
v___x_4087_ = lean_array_uset(v_bs_x27_4082_, v_i_4077_, v___y_4084_);
v_i_4077_ = v___x_4086_;
v_bs_4078_ = v___x_4087_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg___boxed(lean_object* v_sz_4098_, lean_object* v_i_4099_, lean_object* v_bs_4100_){
_start:
{
size_t v_sz_boxed_4101_; size_t v_i_boxed_4102_; lean_object* v_res_4103_; 
v_sz_boxed_4101_ = lean_unbox_usize(v_sz_4098_);
lean_dec(v_sz_4098_);
v_i_boxed_4102_ = lean_unbox_usize(v_i_4099_);
lean_dec(v_i_4099_);
v_res_4103_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_boxed_4101_, v_i_boxed_4102_, v_bs_4100_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(lean_object* v_elems_4104_){
_start:
{
size_t v_sz_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
v_sz_4105_ = lean_array_size(v_elems_4104_);
v___x_4106_ = ((size_t)0ULL);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_4105_, v___x_4106_, v_elems_4104_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(lean_object* v_s_4108_, lean_object* v_elems_4109_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___redArg(v_elems_4109_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray___boxed(lean_object* v_s_4111_, lean_object* v_elems_4112_){
_start:
{
lean_object* v_res_4113_; 
v_res_4113_ = l_Lean_Fmt_Layouts_metaApplication_Term_ofSepArray(v_s_4111_, v_elems_4112_);
lean_dec_ref(v_s_4111_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(lean_object* v_as_4114_, size_t v_sz_4115_, size_t v_i_4116_, lean_object* v_bs_4117_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___redArg(v_sz_4115_, v_i_4116_, v_bs_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0___boxed(lean_object* v_as_4119_, lean_object* v_sz_4120_, lean_object* v_i_4121_, lean_object* v_bs_4122_){
_start:
{
size_t v_sz_boxed_4123_; size_t v_i_boxed_4124_; lean_object* v_res_4125_; 
v_sz_boxed_4123_ = lean_unbox_usize(v_sz_4120_);
lean_dec(v_sz_4120_);
v_i_boxed_4124_ = lean_unbox_usize(v_i_4121_);
lean_dec(v_i_4121_);
v_res_4125_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_Term_ofSepArray_spec__0(v_as_4119_, v_sz_boxed_4123_, v_i_boxed_4124_, v_bs_4122_);
lean_dec_ref(v_as_4119_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(size_t v_sz_4128_, size_t v_i_4129_, lean_object* v_bs_4130_){
_start:
{
uint8_t v___x_4131_; 
v___x_4131_ = lean_usize_dec_lt(v_i_4129_, v_sz_4128_);
if (v___x_4131_ == 0)
{
return v_bs_4130_;
}
else
{
lean_object* v_v_4132_; lean_object* v___x_4133_; lean_object* v_bs_x27_4134_; lean_object* v___y_4136_; 
v_v_4132_ = lean_array_uget(v_bs_4130_, v_i_4129_);
v___x_4133_ = lean_unsigned_to_nat(0u);
v_bs_x27_4134_ = lean_array_uset(v_bs_4130_, v_i_4129_, v___x_4133_);
if (lean_obj_tag(v_v_4132_) == 0)
{
v___y_4136_ = v_v_4132_;
goto v___jp_4135_;
}
else
{
lean_object* v_docs_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4163_; 
v_docs_4141_ = lean_ctor_get(v_v_4132_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v_v_4132_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4143_ = v_v_4132_;
v_isShared_4144_ = v_isSharedCheck_4163_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_docs_4141_);
lean_dec(v_v_4132_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4163_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; uint8_t v___x_4147_; 
v___x_4145_ = lean_array_get_size(v_docs_4141_);
v___x_4146_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4147_ = lean_nat_dec_lt(v___x_4133_, v___x_4145_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; 
lean_del_object(v___x_4143_);
lean_dec_ref(v_docs_4141_);
v___x_4148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_4136_ = v___x_4148_;
goto v___jp_4135_;
}
else
{
uint8_t v___x_4149_; 
v___x_4149_ = lean_nat_dec_le(v___x_4145_, v___x_4145_);
if (v___x_4149_ == 0)
{
if (v___x_4147_ == 0)
{
lean_object* v___x_4150_; 
lean_del_object(v___x_4143_);
lean_dec_ref(v_docs_4141_);
v___x_4150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___closed__0));
v___y_4136_ = v___x_4150_;
goto v___jp_4135_;
}
else
{
size_t v___x_4151_; size_t v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4151_ = ((size_t)0ULL);
v___x_4152_ = lean_usize_of_nat(v___x_4145_);
v___x_4153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_docs_4141_, v___x_4151_, v___x_4152_, v___x_4146_);
lean_dec_ref(v_docs_4141_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4153_);
v___x_4155_ = v___x_4143_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
v___y_4136_ = v___x_4155_;
goto v___jp_4135_;
}
}
}
else
{
size_t v___x_4157_; size_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4157_ = ((size_t)0ULL);
v___x_4158_ = lean_usize_of_nat(v___x_4145_);
v___x_4159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6_spec__6(v_docs_4141_, v___x_4157_, v___x_4158_, v___x_4146_);
lean_dec_ref(v_docs_4141_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4159_);
v___x_4161_ = v___x_4143_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
v___y_4136_ = v___x_4161_;
goto v___jp_4135_;
}
}
}
}
}
v___jp_4135_:
{
size_t v___x_4137_; size_t v___x_4138_; lean_object* v___x_4139_; 
v___x_4137_ = ((size_t)1ULL);
v___x_4138_ = lean_usize_add(v_i_4129_, v___x_4137_);
v___x_4139_ = lean_array_uset(v_bs_x27_4134_, v_i_4129_, v___y_4136_);
v_i_4129_ = v___x_4138_;
v_bs_4130_ = v___x_4139_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1___boxed(lean_object* v_sz_4164_, lean_object* v_i_4165_, lean_object* v_bs_4166_){
_start:
{
size_t v_sz_boxed_4167_; size_t v_i_boxed_4168_; lean_object* v_res_4169_; 
v_sz_boxed_4167_ = lean_unbox_usize(v_sz_4164_);
lean_dec(v_sz_4164_);
v_i_boxed_4168_ = lean_unbox_usize(v_i_4165_);
lean_dec(v_i_4165_);
v_res_4169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_boxed_4167_, v_i_boxed_4168_, v_bs_4166_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(lean_object* v_as_4170_, lean_object* v_j_4171_){
_start:
{
lean_object* v___x_4176_; uint8_t v___x_4177_; 
v___x_4176_ = lean_array_get_size(v_as_4170_);
v___x_4177_ = lean_nat_dec_lt(v_j_4171_, v___x_4176_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; 
lean_dec(v_j_4171_);
v___x_4178_ = lean_box(0);
return v___x_4178_;
}
else
{
lean_object* v___x_4179_; 
v___x_4179_ = lean_array_fget(v_as_4170_, v_j_4171_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_dec_ref_known(v___x_4179_, 1);
goto v___jp_4172_;
}
else
{
lean_object* v_docs_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4190_; 
v_docs_4180_ = lean_ctor_get(v___x_4179_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4179_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4182_ = v___x_4179_;
v_isShared_4183_ = v_isSharedCheck_4190_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_docs_4180_);
lean_dec(v___x_4179_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4190_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; 
v___x_4184_ = lean_array_get_size(v_docs_4180_);
lean_dec_ref(v_docs_4180_);
v___x_4185_ = lean_unsigned_to_nat(0u);
v___x_4186_ = lean_nat_dec_eq(v___x_4184_, v___x_4185_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4188_; 
if (v_isShared_4183_ == 0)
{
lean_ctor_set(v___x_4182_, 0, v_j_4171_);
v___x_4188_ = v___x_4182_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_j_4171_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
else
{
lean_del_object(v___x_4182_);
goto v___jp_4172_;
}
}
}
}
v___jp_4172_:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_unsigned_to_nat(1u);
v___x_4174_ = lean_nat_add(v_j_4171_, v___x_4173_);
lean_dec(v_j_4171_);
v_j_4171_ = v___x_4174_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2___boxed(lean_object* v_as_4191_, lean_object* v_j_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_as_4191_, v_j_4192_);
lean_dec_ref(v_as_4191_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(size_t v_sz_4194_, size_t v_i_4195_, lean_object* v_bs_4196_){
_start:
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_usize_dec_lt(v_i_4195_, v_sz_4194_);
if (v___x_4197_ == 0)
{
return v_bs_4196_;
}
else
{
lean_object* v_v_4198_; lean_object* v___x_4199_; lean_object* v_bs_x27_4200_; lean_object* v___y_4202_; 
v_v_4198_ = lean_array_uget(v_bs_4196_, v_i_4195_);
v___x_4199_ = lean_unsigned_to_nat(0u);
v_bs_x27_4200_ = lean_array_uset(v_bs_4196_, v_i_4195_, v___x_4199_);
if (lean_obj_tag(v_v_4198_) == 0)
{
lean_object* v_doc_4207_; 
v_doc_4207_ = lean_ctor_get(v_v_4198_, 0);
lean_inc_ref(v_doc_4207_);
lean_dec_ref_known(v_v_4198_, 1);
v___y_4202_ = v_doc_4207_;
goto v___jp_4201_;
}
else
{
lean_object* v_docs_4208_; lean_object* v___x_4209_; 
v_docs_4208_ = lean_ctor_get(v_v_4198_, 0);
lean_inc_ref(v_docs_4208_);
lean_dec_ref_known(v_v_4198_, 1);
v___x_4209_ = l_Lean_Fmt_Layouts_fill(v_docs_4208_);
lean_dec_ref(v_docs_4208_);
v___y_4202_ = v___x_4209_;
goto v___jp_4201_;
}
v___jp_4201_:
{
size_t v___x_4203_; size_t v___x_4204_; lean_object* v___x_4205_; 
v___x_4203_ = ((size_t)1ULL);
v___x_4204_ = lean_usize_add(v_i_4195_, v___x_4203_);
v___x_4205_ = lean_array_uset(v_bs_x27_4200_, v_i_4195_, v___y_4202_);
v_i_4195_ = v___x_4204_;
v_bs_4196_ = v___x_4205_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0___boxed(lean_object* v_sz_4210_, lean_object* v_i_4211_, lean_object* v_bs_4212_){
_start:
{
size_t v_sz_boxed_4213_; size_t v_i_boxed_4214_; lean_object* v_res_4215_; 
v_sz_boxed_4213_ = lean_unbox_usize(v_sz_4210_);
lean_dec(v_sz_4210_);
v_i_boxed_4214_ = lean_unbox_usize(v_i_4211_);
lean_dec(v_i_4211_);
v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_boxed_4213_, v_i_boxed_4214_, v_bs_4212_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object* v_lb_4217_, lean_object* v_terms_4218_, lean_object* v_rb_4219_){
_start:
{
lean_object* v_terms_4221_; size_t v_sz_4229_; size_t v___x_4230_; lean_object* v_terms_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; 
v_sz_4229_ = lean_array_size(v_terms_4218_);
v___x_4230_ = ((size_t)0ULL);
v_terms_4231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__1(v_sz_4229_, v___x_4230_, v_terms_4218_);
v___x_4232_ = lean_unsigned_to_nat(1u);
v___x_4233_ = lean_array_get_size(v_terms_4231_);
v___x_4234_ = lean_nat_dec_lt(v___x_4232_, v___x_4233_);
if (v___x_4234_ == 0)
{
v_terms_4221_ = v_terms_4231_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4235_; lean_object* v_firstElemsIdx_x3f_4236_; 
v___x_4235_ = lean_unsigned_to_nat(0u);
v_firstElemsIdx_x3f_4236_ = l_Array_findIdx_x3f_loop___at___00Lean_Fmt_Layouts_metaApplication_spec__2(v_terms_4231_, v___x_4235_);
if (lean_obj_tag(v_firstElemsIdx_x3f_4236_) == 1)
{
lean_object* v_val_4237_; uint8_t v___x_4238_; 
v_val_4237_ = lean_ctor_get(v_firstElemsIdx_x3f_4236_, 0);
lean_inc(v_val_4237_);
lean_dec_ref_known(v_firstElemsIdx_x3f_4236_, 1);
v___x_4238_ = lean_nat_dec_lt(v_val_4237_, v___x_4233_);
if (v___x_4238_ == 0)
{
lean_dec(v_val_4237_);
v_terms_4221_ = v_terms_4231_;
goto v___jp_4220_;
}
else
{
lean_object* v_v_4239_; lean_object* v___x_4240_; lean_object* v_xs_x27_4241_; lean_object* v___y_4243_; 
v_v_4239_ = lean_array_fget(v_terms_4231_, v_val_4237_);
v___x_4240_ = lean_box(0);
v_xs_x27_4241_ = lean_array_fset(v_terms_4231_, v_val_4237_, v___x_4240_);
if (lean_obj_tag(v_v_4239_) == 0)
{
v___y_4243_ = v_v_4239_;
goto v___jp_4242_;
}
else
{
lean_object* v_docs_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v_docs_4245_ = lean_ctor_get(v_v_4239_, 0);
v___x_4246_ = lean_array_get_size(v_docs_4245_);
v___x_4247_ = lean_nat_dec_lt(v___x_4235_, v___x_4246_);
if (v___x_4247_ == 0)
{
v___y_4243_ = v_v_4239_;
goto v___jp_4242_;
}
else
{
lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4258_; 
lean_inc_ref(v_docs_4245_);
v_isSharedCheck_4258_ = !lean_is_exclusive(v_v_4239_);
if (v_isSharedCheck_4258_ == 0)
{
lean_object* v_unused_4259_; 
v_unused_4259_ = lean_ctor_get(v_v_4239_, 0);
lean_dec(v_unused_4259_);
v___x_4249_ = v_v_4239_;
v_isShared_4250_ = v_isSharedCheck_4258_;
goto v_resetjp_4248_;
}
else
{
lean_dec(v_v_4239_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4258_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v_v_4251_; lean_object* v_xs_x27_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4256_; 
v_v_4251_ = lean_array_fget(v_docs_4245_, v___x_4235_);
v_xs_x27_4252_ = lean_array_fset(v_docs_4245_, v___x_4235_, v___x_4240_);
v___x_4253_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4251_);
v___x_4254_ = lean_array_fset(v_xs_x27_4252_, v___x_4235_, v___x_4253_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 0, v___x_4254_);
v___x_4256_ = v___x_4249_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
v___y_4243_ = v___x_4256_;
goto v___jp_4242_;
}
}
}
}
v___jp_4242_:
{
lean_object* v___x_4244_; 
v___x_4244_ = lean_array_fset(v_xs_x27_4241_, v_val_4237_, v___y_4243_);
lean_dec(v_val_4237_);
v_terms_4221_ = v___x_4244_;
goto v___jp_4220_;
}
}
}
else
{
lean_dec(v_firstElemsIdx_x3f_4236_);
v_terms_4221_ = v_terms_4231_;
goto v___jp_4220_;
}
}
v___jp_4220_:
{
lean_object* v___x_4222_; size_t v_sz_4223_; size_t v___x_4224_; lean_object* v_terms_x27_4225_; lean_object* v_terms_x27_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4222_ = ((lean_object*)(l_Lean_Fmt_Layouts_metaApplication___closed__0));
v_sz_4223_ = lean_array_size(v_terms_4221_);
v___x_4224_ = ((size_t)0ULL);
v_terms_x27_4225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_metaApplication_spec__0(v_sz_4223_, v___x_4224_, v_terms_4221_);
v_terms_x27_4226_ = l_Lean_Fmt_Layouts_sepFill(v___x_4222_, v_terms_x27_4225_);
lean_dec_ref(v_terms_x27_4225_);
v___x_4227_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4228_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4217_, v_terms_x27_4226_, v_rb_4219_, v___x_4227_);
return v___x_4228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_pipeOperator(lean_object* v_chain_4262_){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = ((lean_object*)(l_Lean_Fmt_Layouts_pipeOperator___closed__0));
v___x_4264_ = l_Lean_Fmt_Layouts_infixOperator(v_chain_4262_, v___x_4263_);
return v___x_4264_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0(void){
_start:
{
uint8_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; 
v___x_4265_ = 1;
v___x_4266_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4267_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4267_, 0, v___x_4266_);
lean_ctor_set_uint8(v___x_4267_, sizeof(void*)*1, v___x_4265_);
return v___x_4267_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default(void){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = lean_obj_once(&l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0, &l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0_once, _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default___closed__0);
return v___x_4268_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_Types_instInhabitedBlock(void){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_instCoeTaggedDocBlock___lam__0(lean_object* v_block_4270_){
_start:
{
uint8_t v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = 1;
v___x_4272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4272_, 0, v_block_4270_);
lean_ctor_set_uint8(v___x_4272_, sizeof(void*)*1, v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(lean_object* v_val_4275_, uint8_t v___x_4276_, lean_object* v___x_4277_, lean_object* v_____r_4278_, lean_object* v_stickyAcc_4279_){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4280_ = l_Lean_Fmt_TaggedDoc_withStickyAlt_Config_ofSticky(v_val_4275_, v___x_4276_);
v___x_4281_ = l_Lean_Fmt_TaggedDoc_withStickyAlt(v___x_4277_, v_stickyAcc_4279_, v___x_4280_);
lean_dec(v___x_4280_);
v___x_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1___boxed(lean_object* v_val_4283_, lean_object* v___x_4284_, lean_object* v___x_4285_, lean_object* v_____r_4286_, lean_object* v_stickyAcc_4287_){
_start:
{
uint8_t v___x_1444__boxed_4288_; lean_object* v_res_4289_; 
v___x_1444__boxed_4288_ = lean_unbox(v___x_4284_);
v_res_4289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4283_, v___x_1444__boxed_4288_, v___x_4285_, v_____r_4286_, v_stickyAcc_4287_);
lean_dec_ref(v_val_4283_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(lean_object* v_upperBound_4290_, lean_object* v___y_4291_, lean_object* v___x_4292_, lean_object* v_a_4293_, lean_object* v_b_4294_){
_start:
{
uint8_t v___x_4295_; 
v___x_4295_ = lean_nat_dec_lt(v_a_4293_, v_upperBound_4290_);
if (v___x_4295_ == 0)
{
lean_dec(v_a_4293_);
return v_b_4294_;
}
else
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v_block_4298_; uint8_t v_hardNestedIfFirst_4299_; lean_object* v___x_4300_; lean_object* v_a_4302_; lean_object* v___y_4306_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4296_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4297_ = lean_array_get_borrowed(v___x_4296_, v___y_4291_, v_a_4293_);
v_block_4298_ = lean_ctor_get(v___x_4297_, 0);
v_hardNestedIfFirst_4299_ = lean_ctor_get_uint8(v___x_4297_, sizeof(void*)*1);
v___x_4300_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_b_4294_);
v___x_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4309_, 0, v_b_4294_);
v___x_4310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_4311_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4309_, v___x_4310_);
v___x_4312_ = lean_box(0);
lean_inc_ref_n(v_block_4298_, 2);
v___x_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4313_, 0, v_block_4298_);
v___x_4314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
lean_ctor_set(v___x_4314_, 2, v___x_4312_);
v___x_4315_ = lean_unsigned_to_nat(2u);
v___x_4316_ = lean_mk_empty_array_with_capacity(v___x_4315_);
lean_inc_ref(v___x_4316_);
v___x_4317_ = lean_array_push(v___x_4316_, v___x_4311_);
v___x_4318_ = lean_array_push(v___x_4317_, v___x_4314_);
v___x_4319_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4318_);
lean_dec_ref(v___x_4318_);
v___x_4320_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4319_);
v___x_4321_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_block_4298_);
if (lean_obj_tag(v___x_4321_) == 1)
{
lean_object* v_val_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4346_; 
v_val_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4346_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_val_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4346_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v_stickyVariant_4326_; lean_object* v___x_4327_; lean_object* v___x_4329_; 
v_stickyVariant_4326_ = lean_ctor_get(v_val_4322_, 0);
v___x_4327_ = l_Lean_Fmt_TaggedDoc_flattened(v_b_4294_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v___x_4327_);
v___x_4329_ = v___x_4324_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_4331_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4329_, v___x_4330_);
lean_inc_ref(v_stickyVariant_4326_);
v___x_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4332_, 0, v_stickyVariant_4326_);
v___x_4333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4312_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
lean_ctor_set(v___x_4333_, 2, v___x_4312_);
v___x_4334_ = lean_array_push(v___x_4316_, v___x_4331_);
v___x_4335_ = lean_array_push(v___x_4334_, v___x_4333_);
v___x_4336_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4335_);
lean_dec_ref(v___x_4335_);
if (v_hardNestedIfFirst_4299_ == 0)
{
goto v___jp_4337_;
}
else
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = lean_nat_sub(v___x_4292_, v___x_4300_);
v___x_4341_ = lean_nat_dec_lt(v_a_4293_, v___x_4340_);
lean_dec(v___x_4340_);
if (v___x_4341_ == 0)
{
goto v___jp_4337_;
}
else
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4342_ = l_Lean_Fmt_TaggedDoc_hardNested(v___x_4336_);
v___x_4343_ = lean_box(0);
v___x_4344_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4322_, v___x_4295_, v___x_4320_, v___x_4343_, v___x_4342_);
lean_dec(v_val_4322_);
v___y_4306_ = v___x_4344_;
goto v___jp_4305_;
}
}
v___jp_4337_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = lean_box(0);
v___x_4339_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___lam__1(v_val_4322_, v___x_4295_, v___x_4320_, v___x_4338_, v___x_4336_);
lean_dec(v_val_4322_);
v___y_4306_ = v___x_4339_;
goto v___jp_4305_;
}
}
}
}
else
{
lean_dec(v___x_4321_);
lean_dec_ref(v___x_4316_);
lean_dec_ref(v_b_4294_);
v_a_4302_ = v___x_4320_;
goto v___jp_4301_;
}
v___jp_4301_:
{
lean_object* v___x_4303_; 
v___x_4303_ = lean_nat_add(v_a_4293_, v___x_4300_);
lean_dec(v_a_4293_);
v_a_4293_ = v___x_4303_;
v_b_4294_ = v_a_4302_;
goto _start;
}
v___jp_4305_:
{
if (lean_obj_tag(v___y_4306_) == 0)
{
lean_object* v_a_4307_; 
lean_dec(v_a_4293_);
v_a_4307_ = lean_ctor_get(v___y_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___y_4306_, 1);
return v_a_4307_;
}
else
{
lean_object* v_a_4308_; 
v_a_4308_ = lean_ctor_get(v___y_4306_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___y_4306_, 1);
v_a_4302_ = v_a_4308_;
goto v___jp_4301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg___boxed(lean_object* v_upperBound_4347_, lean_object* v___y_4348_, lean_object* v___x_4349_, lean_object* v_a_4350_, lean_object* v_b_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4347_, v___y_4348_, v___x_4349_, v_a_4350_, v_b_4351_);
lean_dec(v___x_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v_upperBound_4347_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(lean_object* v_as_4353_, size_t v_i_4354_, size_t v_stop_4355_, lean_object* v_b_4356_){
_start:
{
lean_object* v___y_4358_; uint8_t v___x_4362_; 
v___x_4362_ = lean_usize_dec_eq(v_i_4354_, v_stop_4355_);
if (v___x_4362_ == 0)
{
lean_object* v___x_4363_; lean_object* v_block_4364_; uint8_t v___x_4365_; 
v___x_4363_ = lean_array_uget_borrowed(v_as_4353_, v_i_4354_);
v_block_4364_ = lean_ctor_get(v___x_4363_, 0);
v___x_4365_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_block_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
lean_inc(v___x_4363_);
v___x_4366_ = lean_array_push(v_b_4356_, v___x_4363_);
v___y_4358_ = v___x_4366_;
goto v___jp_4357_;
}
else
{
v___y_4358_ = v_b_4356_;
goto v___jp_4357_;
}
}
else
{
return v_b_4356_;
}
v___jp_4357_:
{
size_t v___x_4359_; size_t v___x_4360_; 
v___x_4359_ = ((size_t)1ULL);
v___x_4360_ = lean_usize_add(v_i_4354_, v___x_4359_);
v_i_4354_ = v___x_4360_;
v_b_4356_ = v___y_4358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1___boxed(lean_object* v_as_4367_, lean_object* v_i_4368_, lean_object* v_stop_4369_, lean_object* v_b_4370_){
_start:
{
size_t v_i_boxed_4371_; size_t v_stop_boxed_4372_; lean_object* v_res_4373_; 
v_i_boxed_4371_ = lean_unbox_usize(v_i_4368_);
lean_dec(v_i_4368_);
v_stop_boxed_4372_ = lean_unbox_usize(v_stop_4369_);
lean_dec(v_stop_4369_);
v_res_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_as_4367_, v_i_boxed_4371_, v_stop_boxed_4372_, v_b_4370_);
lean_dec_ref(v_as_4367_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks(lean_object* v_blocks_4376_, uint8_t v_format_4377_){
_start:
{
lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___y_4388_; lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; 
v___x_4385_ = l_Lean_Fmt_Layouts_Types_instInhabitedBlock_default;
v___x_4386_ = lean_unsigned_to_nat(0u);
v___x_4398_ = lean_array_get_size(v_blocks_4376_);
v___x_4399_ = ((lean_object*)(l_Lean_Fmt_Layouts_blocks___closed__0));
v___x_4400_ = lean_nat_dec_lt(v___x_4386_, v___x_4398_);
if (v___x_4400_ == 0)
{
v___y_4388_ = v___x_4399_;
goto v___jp_4387_;
}
else
{
uint8_t v___x_4401_; 
v___x_4401_ = lean_nat_dec_le(v___x_4398_, v___x_4398_);
if (v___x_4401_ == 0)
{
if (v___x_4400_ == 0)
{
v___y_4388_ = v___x_4399_;
goto v___jp_4387_;
}
else
{
size_t v___x_4402_; size_t v___x_4403_; lean_object* v___x_4404_; 
v___x_4402_ = ((size_t)0ULL);
v___x_4403_ = lean_usize_of_nat(v___x_4398_);
v___x_4404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4376_, v___x_4402_, v___x_4403_, v___x_4399_);
v___y_4388_ = v___x_4404_;
goto v___jp_4387_;
}
}
else
{
size_t v___x_4405_; size_t v___x_4406_; lean_object* v___x_4407_; 
v___x_4405_ = ((size_t)0ULL);
v___x_4406_ = lean_usize_of_nat(v___x_4398_);
v___x_4407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_blocks_spec__1(v_blocks_4376_, v___x_4405_, v___x_4406_, v___x_4399_);
v___y_4388_ = v___x_4407_;
goto v___jp_4387_;
}
}
v___jp_4378_:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v___y_4380_, v___y_4381_, v___y_4380_, v___y_4379_, v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
if (v_format_4377_ == 0)
{
return v___x_4383_;
}
else
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4383_);
return v___x_4384_;
}
}
v___jp_4387_:
{
lean_object* v___x_4389_; uint8_t v___x_4390_; 
v___x_4389_ = lean_array_get_size(v___y_4388_);
v___x_4390_ = lean_nat_dec_eq(v___x_4389_, v___x_4386_);
if (v___x_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v_block_4392_; uint8_t v_hardNestedIfFirst_4393_; lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4391_ = lean_array_get_borrowed(v___x_4385_, v___y_4388_, v___x_4386_);
v_block_4392_ = lean_ctor_get(v___x_4391_, 0);
v_hardNestedIfFirst_4393_ = lean_ctor_get_uint8(v___x_4391_, sizeof(void*)*1);
v___x_4394_ = lean_unsigned_to_nat(1u);
v___x_4395_ = lean_nat_dec_eq(v___x_4389_, v___x_4394_);
if (v___x_4395_ == 0)
{
if (v_hardNestedIfFirst_4393_ == 0)
{
lean_inc_ref(v_block_4392_);
v___y_4379_ = v___x_4394_;
v___y_4380_ = v___x_4389_;
v___y_4381_ = v___y_4388_;
v___y_4382_ = v_block_4392_;
goto v___jp_4378_;
}
else
{
lean_object* v___x_4396_; 
lean_inc_ref(v_block_4392_);
v___x_4396_ = l_Lean_Fmt_TaggedDoc_hardNested(v_block_4392_);
v___y_4379_ = v___x_4394_;
v___y_4380_ = v___x_4389_;
v___y_4381_ = v___y_4388_;
v___y_4382_ = v___x_4396_;
goto v___jp_4378_;
}
}
else
{
lean_inc_ref(v_block_4392_);
lean_dec_ref(v___y_4388_);
return v_block_4392_;
}
}
else
{
lean_object* v___x_4397_; 
lean_dec_ref(v___y_4388_);
v___x_4397_ = l_Lean_Fmt_TaggedDoc_empty;
return v___x_4397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_blocks___boxed(lean_object* v_blocks_4408_, lean_object* v_format_4409_){
_start:
{
uint8_t v_format_boxed_4410_; lean_object* v_res_4411_; 
v_format_boxed_4410_ = lean_unbox(v_format_4409_);
v_res_4411_ = l_Lean_Fmt_Layouts_blocks(v_blocks_4408_, v_format_boxed_4410_);
lean_dec_ref(v_blocks_4408_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(lean_object* v_upperBound_4412_, lean_object* v___y_4413_, lean_object* v___x_4414_, lean_object* v_inst_4415_, lean_object* v_R_4416_, lean_object* v_a_4417_, lean_object* v_b_4418_, lean_object* v_c_4419_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___redArg(v_upperBound_4412_, v___y_4413_, v___x_4414_, v_a_4417_, v_b_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0___boxed(lean_object* v_upperBound_4421_, lean_object* v___y_4422_, lean_object* v___x_4423_, lean_object* v_inst_4424_, lean_object* v_R_4425_, lean_object* v_a_4426_, lean_object* v_b_4427_, lean_object* v_c_4428_){
_start:
{
lean_object* v_res_4429_; 
v_res_4429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Layouts_blocks_spec__0(v_upperBound_4421_, v___y_4422_, v___x_4423_, v_inst_4424_, v_R_4425_, v_a_4426_, v_b_4427_, v_c_4428_);
lean_dec(v___x_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v_upperBound_4421_);
return v_res_4429_;
}
}
static lean_object* _init_l_Lean_Fmt_Layouts_tuple___closed__0(void){
_start:
{
uint8_t v___x_4430_; uint8_t v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4430_ = 0;
v___x_4431_ = 1;
v___x_4432_ = l_Lean_Fmt_TaggedDoc_break;
v___x_4433_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
lean_ctor_set_uint8(v___x_4433_, sizeof(void*)*1, v___x_4431_);
lean_ctor_set_uint8(v___x_4433_, sizeof(void*)*1 + 1, v___x_4430_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple(lean_object* v_sep_4434_, lean_object* v_lb_4435_, lean_object* v_fields_4436_, lean_object* v_rb_4437_){
_start:
{
uint8_t v___x_4438_; lean_object* v_fields_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; uint8_t v___x_4442_; 
v___x_4438_ = 1;
lean_inc_ref(v_sep_4434_);
v_fields_4439_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4434_, v_fields_4436_, v___x_4438_);
v___x_4440_ = lean_array_get_size(v_fields_4439_);
v___x_4441_ = lean_unsigned_to_nat(1u);
v___x_4442_ = lean_nat_dec_eq(v___x_4440_, v___x_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; lean_object* v_fields_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4443_ = lean_obj_once(&l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2, &l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2_once, _init_l_Lean_Fmt_Layouts_sepHorizontalOrVertical___closed__2);
v_fields_4444_ = l_Lean_Fmt_Layouts_sepArray(v_sep_4434_, v_fields_4439_, v___x_4443_);
lean_dec_ref(v_fields_4439_);
v___x_4445_ = lean_obj_once(&l_Lean_Fmt_Layouts_tuple___closed__0, &l_Lean_Fmt_Layouts_tuple___closed__0_once, _init_l_Lean_Fmt_Layouts_tuple___closed__0);
v___x_4446_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4435_, v_fields_4444_, v_rb_4437_, v___x_4445_);
return v___x_4446_;
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_dec_ref(v_sep_4434_);
v___x_4447_ = l_Lean_Fmt_instInhabitedTaggedDoc_default;
v___x_4448_ = lean_unsigned_to_nat(0u);
v___x_4449_ = lean_array_get(v___x_4447_, v_fields_4439_, v___x_4448_);
lean_dec_ref(v_fields_4439_);
v___x_4450_ = ((lean_object*)(l_Lean_Fmt_Layouts_parens___closed__0));
v___x_4451_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4435_, v___x_4449_, v_rb_4437_, v___x_4450_);
return v___x_4451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_tuple___boxed(lean_object* v_sep_4452_, lean_object* v_lb_4453_, lean_object* v_fields_4454_, lean_object* v_rb_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l_Lean_Fmt_Layouts_tuple(v_sep_4452_, v_lb_4453_, v_fields_4454_, v_rb_4455_);
lean_dec_ref(v_fields_4454_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection(lean_object* v_sep_4457_, lean_object* v_lb_4458_, lean_object* v_elems_4459_, lean_object* v_rb_4460_, lean_object* v_format_4461_){
_start:
{
uint8_t v_spacing_4462_; uint8_t v_unindentedRb_4463_; uint8_t v___x_4464_; lean_object* v_elems_4465_; lean_object* v___y_4467_; 
v_spacing_4462_ = lean_ctor_get_uint8(v_format_4461_, 0);
v_unindentedRb_4463_ = lean_ctor_get_uint8(v_format_4461_, 1);
v___x_4464_ = 1;
lean_inc_ref(v_sep_4457_);
v_elems_4465_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_sepArray_normalize(v_sep_4457_, v_elems_4459_, v___x_4464_);
if (v_spacing_4462_ == 0)
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Lean_Fmt_TaggedDoc_break;
v___y_4467_ = v___x_4472_;
goto v___jp_4466_;
}
else
{
lean_object* v___x_4473_; 
v___x_4473_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4467_ = v___x_4473_;
goto v___jp_4466_;
}
v___jp_4466_:
{
lean_object* v_fields_4468_; uint8_t v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v_fields_4468_ = l_Lean_Fmt_Layouts_sepFill(v_sep_4457_, v_elems_4465_);
lean_dec_ref(v_elems_4465_);
v___x_4469_ = 1;
lean_inc_ref(v___y_4467_);
v___x_4470_ = lean_alloc_ctor(1, 1, 2);
lean_ctor_set(v___x_4470_, 0, v___y_4467_);
lean_ctor_set_uint8(v___x_4470_, sizeof(void*)*1, v_unindentedRb_4463_);
lean_ctor_set_uint8(v___x_4470_, sizeof(void*)*1 + 1, v___x_4469_);
v___x_4471_ = l_Lean_Fmt_Layouts_bracketed(v_lb_4458_, v_fields_4468_, v_rb_4460_, v___x_4470_);
return v___x_4471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_collection___boxed(lean_object* v_sep_4474_, lean_object* v_lb_4475_, lean_object* v_elems_4476_, lean_object* v_rb_4477_, lean_object* v_format_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_Fmt_Layouts_collection(v_sep_4474_, v_lb_4475_, v_elems_4476_, v_rb_4477_, v_format_4478_);
lean_dec_ref(v_format_4478_);
lean_dec_ref(v_elems_4476_);
return v_res_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0(lean_object* v_keyword_4480_, lean_object* v_collection_4481_){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4482_ = lean_unsigned_to_nat(2u);
v___x_4483_ = lean_mk_empty_array_with_capacity(v___x_4482_);
v___x_4484_ = lean_array_push(v___x_4483_, v_keyword_4480_);
v___x_4485_ = lean_array_push(v___x_4484_, v_collection_4481_);
v___x_4486_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4485_);
lean_dec_ref(v___x_4485_);
v___x_4487_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4486_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection(lean_object* v_sep_4488_, lean_object* v_keyword_4489_, lean_object* v_lb_4490_, lean_object* v_elems_4491_, lean_object* v_rb_4492_, lean_object* v_format_4493_){
_start:
{
lean_object* v___f_4494_; lean_object* v_collection_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___f_4494_ = lean_alloc_closure((void*)(l_Lean_Fmt_Layouts_keywordPrefixedCollection___lam__0), 2, 1);
lean_closure_set(v___f_4494_, 0, v_keyword_4489_);
v_collection_4495_ = l_Lean_Fmt_Layouts_collection(v_sep_4488_, v_lb_4490_, v_elems_4491_, v_rb_4492_, v_format_4493_);
v___x_4496_ = lean_box(0);
v___x_4497_ = l_Lean_Fmt_TaggedDoc_propagateStickyness(v_collection_4495_, v___f_4494_, v___x_4496_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_keywordPrefixedCollection___boxed(lean_object* v_sep_4498_, lean_object* v_keyword_4499_, lean_object* v_lb_4500_, lean_object* v_elems_4501_, lean_object* v_rb_4502_, lean_object* v_format_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_Fmt_Layouts_keywordPrefixedCollection(v_sep_4498_, v_keyword_4499_, v_lb_4500_, v_elems_4501_, v_rb_4502_, v_format_4503_);
lean_dec_ref(v_format_4503_);
lean_dec_ref(v_elems_4501_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(uint8_t v_x_4505_){
_start:
{
if (v_x_4505_ == 0)
{
lean_object* v___x_4506_; 
v___x_4506_ = lean_unsigned_to_nat(0u);
return v___x_4506_;
}
else
{
lean_object* v___x_4507_; 
v___x_4507_ = lean_unsigned_to_nat(1u);
return v___x_4507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx___boxed(lean_object* v_x_4508_){
_start:
{
uint8_t v_x_boxed_4509_; lean_object* v_res_4510_; 
v_x_boxed_4509_ = lean_unbox(v_x_4508_);
v_res_4510_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorIdx(v_x_boxed_4509_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(lean_object* v_k_4511_){
_start:
{
lean_inc(v_k_4511_);
return v_k_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg___boxed(lean_object* v_k_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___redArg(v_k_4512_);
lean_dec(v_k_4512_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(lean_object* v_motive_4514_, lean_object* v_ctorIdx_4515_, uint8_t v_t_4516_, lean_object* v_h_4517_, lean_object* v_k_4518_){
_start:
{
lean_inc(v_k_4518_);
return v_k_4518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim___boxed(lean_object* v_motive_4519_, lean_object* v_ctorIdx_4520_, lean_object* v_t_4521_, lean_object* v_h_4522_, lean_object* v_k_4523_){
_start:
{
uint8_t v_t_boxed_4524_; lean_object* v_res_4525_; 
v_t_boxed_4524_ = lean_unbox(v_t_4521_);
v_res_4525_ = l_Lean_Fmt_Layouts_Types_SignatureKind_ctorElim(v_motive_4519_, v_ctorIdx_4520_, v_t_boxed_4524_, v_h_4522_, v_k_4523_);
lean_dec(v_k_4523_);
lean_dec(v_ctorIdx_4520_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(lean_object* v_local_4526_){
_start:
{
lean_inc(v_local_4526_);
return v_local_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg___boxed(lean_object* v_local_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___redArg(v_local_4527_);
lean_dec(v_local_4527_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(lean_object* v_motive_4529_, uint8_t v_t_4530_, lean_object* v_h_4531_, lean_object* v_local_4532_){
_start:
{
lean_inc(v_local_4532_);
return v_local_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim___boxed(lean_object* v_motive_4533_, lean_object* v_t_4534_, lean_object* v_h_4535_, lean_object* v_local_4536_){
_start:
{
uint8_t v_t_boxed_4537_; lean_object* v_res_4538_; 
v_t_boxed_4537_ = lean_unbox(v_t_4534_);
v_res_4538_ = l_Lean_Fmt_Layouts_Types_SignatureKind_local_elim(v_motive_4533_, v_t_boxed_4537_, v_h_4535_, v_local_4536_);
lean_dec(v_local_4536_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(lean_object* v_global_4539_){
_start:
{
lean_inc(v_global_4539_);
return v_global_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg___boxed(lean_object* v_global_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___redArg(v_global_4540_);
lean_dec(v_global_4540_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(lean_object* v_motive_4542_, uint8_t v_t_4543_, lean_object* v_h_4544_, lean_object* v_global_4545_){
_start:
{
lean_inc(v_global_4545_);
return v_global_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim___boxed(lean_object* v_motive_4546_, lean_object* v_t_4547_, lean_object* v_h_4548_, lean_object* v_global_4549_){
_start:
{
uint8_t v_t_boxed_4550_; lean_object* v_res_4551_; 
v_t_boxed_4550_ = lean_unbox(v_t_4547_);
v_res_4551_ = l_Lean_Fmt_Layouts_Types_SignatureKind_global_elim(v_motive_4546_, v_t_boxed_4550_, v_h_4548_, v_global_4549_);
lean_dec(v_global_4549_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(lean_object* v_as_4552_, size_t v_i_4553_, size_t v_stop_4554_, lean_object* v_b_4555_){
_start:
{
lean_object* v___y_4557_; uint8_t v___x_4561_; 
v___x_4561_ = lean_usize_dec_eq(v_i_4553_, v_stop_4554_);
if (v___x_4561_ == 0)
{
lean_object* v___x_4562_; lean_object* v___y_4564_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; 
v___x_4562_ = lean_unsigned_to_nat(0u);
v___x_4568_ = lean_array_uget_borrowed(v_as_4552_, v_i_4553_);
v___x_4569_ = lean_array_get_size(v___x_4568_);
v___x_4570_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4571_ = lean_nat_dec_lt(v___x_4562_, v___x_4569_);
if (v___x_4571_ == 0)
{
v___y_4564_ = v___x_4570_;
goto v___jp_4563_;
}
else
{
uint8_t v___x_4572_; 
v___x_4572_ = lean_nat_dec_le(v___x_4569_, v___x_4569_);
if (v___x_4572_ == 0)
{
if (v___x_4571_ == 0)
{
v___y_4564_ = v___x_4570_;
goto v___jp_4563_;
}
else
{
size_t v___x_4573_; size_t v___x_4574_; lean_object* v___x_4575_; 
v___x_4573_ = ((size_t)0ULL);
v___x_4574_ = lean_usize_of_nat(v___x_4569_);
v___x_4575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v___x_4568_, v___x_4573_, v___x_4574_, v___x_4570_);
v___y_4564_ = v___x_4575_;
goto v___jp_4563_;
}
}
else
{
size_t v___x_4576_; size_t v___x_4577_; lean_object* v___x_4578_; 
v___x_4576_ = ((size_t)0ULL);
v___x_4577_ = lean_usize_of_nat(v___x_4569_);
v___x_4578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v___x_4568_, v___x_4576_, v___x_4577_, v___x_4570_);
v___y_4564_ = v___x_4578_;
goto v___jp_4563_;
}
}
v___jp_4563_:
{
lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4565_ = lean_array_get_size(v___y_4564_);
v___x_4566_ = lean_nat_dec_eq(v___x_4565_, v___x_4562_);
if (v___x_4566_ == 0)
{
lean_object* v___x_4567_; 
v___x_4567_ = lean_array_push(v_b_4555_, v___y_4564_);
v___y_4557_ = v___x_4567_;
goto v___jp_4556_;
}
else
{
lean_dec_ref(v___y_4564_);
v___y_4557_ = v_b_4555_;
goto v___jp_4556_;
}
}
}
else
{
return v_b_4555_;
}
v___jp_4556_:
{
size_t v___x_4558_; size_t v___x_4559_; 
v___x_4558_ = ((size_t)1ULL);
v___x_4559_ = lean_usize_add(v_i_4553_, v___x_4558_);
v_i_4553_ = v___x_4559_;
v_b_4555_ = v___y_4557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0___boxed(lean_object* v_as_4579_, lean_object* v_i_4580_, lean_object* v_stop_4581_, lean_object* v_b_4582_){
_start:
{
size_t v_i_boxed_4583_; size_t v_stop_boxed_4584_; lean_object* v_res_4585_; 
v_i_boxed_4583_ = lean_unbox_usize(v_i_4580_);
lean_dec(v_i_4580_);
v_stop_boxed_4584_ = lean_unbox_usize(v_stop_4581_);
lean_dec(v_stop_4581_);
v_res_4585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(v_as_4579_, v_i_boxed_4583_, v_stop_boxed_4584_, v_b_4582_);
lean_dec_ref(v_as_4579_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(lean_object* v_as_4588_, lean_object* v_start_4589_, lean_object* v_stop_4590_){
_start:
{
lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4591_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___closed__0));
v___x_4592_ = lean_nat_dec_lt(v_start_4589_, v_stop_4590_);
if (v___x_4592_ == 0)
{
return v___x_4591_;
}
else
{
lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4593_ = lean_array_get_size(v_as_4588_);
v___x_4594_ = lean_nat_dec_le(v_stop_4590_, v___x_4593_);
if (v___x_4594_ == 0)
{
uint8_t v___x_4595_; 
v___x_4595_ = lean_nat_dec_lt(v_start_4589_, v___x_4593_);
if (v___x_4595_ == 0)
{
return v___x_4591_;
}
else
{
size_t v___x_4596_; size_t v___x_4597_; lean_object* v___x_4598_; 
v___x_4596_ = lean_usize_of_nat(v_start_4589_);
v___x_4597_ = lean_usize_of_nat(v___x_4593_);
v___x_4598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(v_as_4588_, v___x_4596_, v___x_4597_, v___x_4591_);
return v___x_4598_;
}
}
else
{
size_t v___x_4599_; size_t v___x_4600_; lean_object* v___x_4601_; 
v___x_4599_ = lean_usize_of_nat(v_start_4589_);
v___x_4600_ = lean_usize_of_nat(v_stop_4590_);
v___x_4601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0_spec__0(v_as_4588_, v___x_4599_, v___x_4600_, v___x_4591_);
return v___x_4601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0___boxed(lean_object* v_as_4602_, lean_object* v_start_4603_, lean_object* v_stop_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v_as_4602_, v_start_4603_, v_stop_4604_);
lean_dec(v_stop_4604_);
lean_dec(v_start_4603_);
lean_dec_ref(v_as_4602_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(lean_object* v_as_4606_, size_t v_i_4607_, size_t v_stop_4608_, lean_object* v_b_4609_){
_start:
{
lean_object* v___y_4611_; uint8_t v___x_4615_; 
v___x_4615_ = lean_usize_dec_eq(v_i_4607_, v_stop_4608_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v_group_4619_; lean_object* v___x_4620_; uint8_t v___x_4621_; 
v___x_4616_ = lean_unsigned_to_nat(0u);
v___x_4617_ = lean_array_uget_borrowed(v_as_4606_, v_i_4607_);
v___x_4618_ = lean_array_get_size(v___x_4617_);
v_group_4619_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__0(v___x_4617_, v___x_4616_, v___x_4618_);
v___x_4620_ = lean_array_get_size(v_group_4619_);
v___x_4621_ = lean_nat_dec_eq(v___x_4620_, v___x_4616_);
if (v___x_4621_ == 0)
{
lean_object* v___x_4622_; 
v___x_4622_ = lean_array_push(v_b_4609_, v_group_4619_);
v___y_4611_ = v___x_4622_;
goto v___jp_4610_;
}
else
{
lean_dec_ref(v_group_4619_);
v___y_4611_ = v_b_4609_;
goto v___jp_4610_;
}
}
else
{
return v_b_4609_;
}
v___jp_4610_:
{
size_t v___x_4612_; size_t v___x_4613_; 
v___x_4612_ = ((size_t)1ULL);
v___x_4613_ = lean_usize_add(v_i_4607_, v___x_4612_);
v_i_4607_ = v___x_4613_;
v_b_4609_ = v___y_4611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2___boxed(lean_object* v_as_4623_, lean_object* v_i_4624_, lean_object* v_stop_4625_, lean_object* v_b_4626_){
_start:
{
size_t v_i_boxed_4627_; size_t v_stop_boxed_4628_; lean_object* v_res_4629_; 
v_i_boxed_4627_ = lean_unbox_usize(v_i_4624_);
lean_dec(v_i_4624_);
v_stop_boxed_4628_ = lean_unbox_usize(v_stop_4625_);
lean_dec(v_stop_4625_);
v_res_4629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(v_as_4623_, v_i_boxed_4627_, v_stop_boxed_4628_, v_b_4626_);
lean_dec_ref(v_as_4623_);
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(lean_object* v_as_4632_, lean_object* v_start_4633_, lean_object* v_stop_4634_){
_start:
{
lean_object* v___x_4635_; uint8_t v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___closed__0));
v___x_4636_ = lean_nat_dec_lt(v_start_4633_, v_stop_4634_);
if (v___x_4636_ == 0)
{
return v___x_4635_;
}
else
{
lean_object* v___x_4637_; uint8_t v___x_4638_; 
v___x_4637_ = lean_array_get_size(v_as_4632_);
v___x_4638_ = lean_nat_dec_le(v_stop_4634_, v___x_4637_);
if (v___x_4638_ == 0)
{
uint8_t v___x_4639_; 
v___x_4639_ = lean_nat_dec_lt(v_start_4633_, v___x_4637_);
if (v___x_4639_ == 0)
{
return v___x_4635_;
}
else
{
size_t v___x_4640_; size_t v___x_4641_; lean_object* v___x_4642_; 
v___x_4640_ = lean_usize_of_nat(v_start_4633_);
v___x_4641_ = lean_usize_of_nat(v___x_4637_);
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(v_as_4632_, v___x_4640_, v___x_4641_, v___x_4635_);
return v___x_4642_;
}
}
else
{
size_t v___x_4643_; size_t v___x_4644_; lean_object* v___x_4645_; 
v___x_4643_ = lean_usize_of_nat(v_start_4633_);
v___x_4644_ = lean_usize_of_nat(v_stop_4634_);
v___x_4645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1_spec__2(v_as_4632_, v___x_4643_, v___x_4644_, v___x_4635_);
return v___x_4645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1___boxed(lean_object* v_as_4646_, lean_object* v_start_4647_, lean_object* v_stop_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_as_4646_, v_start_4647_, v_stop_4648_);
lean_dec(v_stop_4648_);
lean_dec(v_start_4647_);
lean_dec_ref(v_as_4646_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(size_t v_sz_4650_, size_t v_i_4651_, lean_object* v_bs_4652_){
_start:
{
uint8_t v___x_4653_; 
v___x_4653_ = lean_usize_dec_lt(v_i_4651_, v_sz_4650_);
if (v___x_4653_ == 0)
{
return v_bs_4652_;
}
else
{
lean_object* v_v_4654_; lean_object* v___x_4655_; lean_object* v_bs_x27_4656_; lean_object* v___x_4657_; size_t v___x_4658_; size_t v___x_4659_; lean_object* v___x_4660_; 
v_v_4654_ = lean_array_uget(v_bs_4652_, v_i_4651_);
v___x_4655_ = lean_unsigned_to_nat(0u);
v_bs_x27_4656_ = lean_array_uset(v_bs_4652_, v_i_4651_, v___x_4655_);
v___x_4657_ = l_Lean_Fmt_TaggedDoc_fillUsingSpaceWithSoftBoundaries(v_v_4654_);
v___x_4658_ = ((size_t)1ULL);
v___x_4659_ = lean_usize_add(v_i_4651_, v___x_4658_);
v___x_4660_ = lean_array_uset(v_bs_x27_4656_, v_i_4651_, v___x_4657_);
v_i_4651_ = v___x_4659_;
v_bs_4652_ = v___x_4660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2___boxed(lean_object* v_sz_4662_, lean_object* v_i_4663_, lean_object* v_bs_4664_){
_start:
{
size_t v_sz_boxed_4665_; size_t v_i_boxed_4666_; lean_object* v_res_4667_; 
v_sz_boxed_4665_ = lean_unbox_usize(v_sz_4662_);
lean_dec(v_sz_4662_);
v_i_boxed_4666_ = lean_unbox_usize(v_i_4663_);
lean_dec(v_i_4663_);
v_res_4667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_sz_boxed_4665_, v_i_boxed_4666_, v_bs_4664_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(lean_object* v_lvals_4668_, lean_object* v_binderGroups_4669_, lean_object* v_typeAscriptionTk_4670_, lean_object* v_type_4671_, uint8_t v_kind_4672_, lean_object* v_lvalsLayout_4673_){
_start:
{
lean_object* v___y_4675_; lean_object* v___y_4676_; uint8_t v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4692_; uint8_t v___y_4693_; lean_object* v___y_4694_; lean_object* v___x_4699_; lean_object* v___y_4701_; lean_object* v___y_4702_; uint8_t v___y_4703_; lean_object* v___y_4713_; lean_object* v___x_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; 
v___x_4699_ = lean_unsigned_to_nat(0u);
v___x_4723_ = lean_array_get_size(v_lvals_4668_);
v___x_4724_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v___x_4725_ = lean_nat_dec_lt(v___x_4699_, v___x_4723_);
if (v___x_4725_ == 0)
{
v___y_4713_ = v___x_4724_;
goto v___jp_4712_;
}
else
{
uint8_t v___x_4726_; 
v___x_4726_ = lean_nat_dec_le(v___x_4723_, v___x_4723_);
if (v___x_4726_ == 0)
{
if (v___x_4725_ == 0)
{
v___y_4713_ = v___x_4724_;
goto v___jp_4712_;
}
else
{
size_t v___x_4727_; size_t v___x_4728_; lean_object* v___x_4729_; 
v___x_4727_ = ((size_t)0ULL);
v___x_4728_ = lean_usize_of_nat(v___x_4723_);
v___x_4729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_lvals_4668_, v___x_4727_, v___x_4728_, v___x_4724_);
v___y_4713_ = v___x_4729_;
goto v___jp_4712_;
}
}
else
{
size_t v___x_4730_; size_t v___x_4731_; lean_object* v___x_4732_; 
v___x_4730_ = ((size_t)0ULL);
v___x_4731_ = lean_usize_of_nat(v___x_4723_);
v___x_4732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_array_spec__6(v_lvals_4668_, v___x_4730_, v___x_4731_, v___x_4724_);
v___y_4713_ = v___x_4732_;
goto v___jp_4712_;
}
}
v___jp_4674_:
{
size_t v_sz_4679_; size_t v___x_4680_; lean_object* v___x_4681_; lean_object* v_binderGroups_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
v_sz_4679_ = lean_array_size(v___y_4675_);
v___x_4680_ = ((size_t)0ULL);
v___x_4681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__2(v_sz_4679_, v___x_4680_, v___y_4675_);
v_binderGroups_4682_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4681_, v___y_4677_);
lean_dec_ref(v___x_4681_);
v___x_4683_ = lean_apply_1(v_lvalsLayout_4673_, v___y_4676_);
v___x_4684_ = lean_unsigned_to_nat(2u);
v___x_4685_ = lean_mk_empty_array_with_capacity(v___x_4684_);
v___x_4686_ = lean_array_push(v___x_4685_, v___x_4683_);
v___x_4687_ = lean_array_push(v___x_4686_, v_binderGroups_4682_);
v___x_4688_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v___x_4687_, v___y_4677_);
lean_dec_ref(v___x_4687_);
v___x_4689_ = l_Lean_Fmt_Layouts_typeAscription(v___x_4688_, v_typeAscriptionTk_4670_, v_type_4671_, v___y_4678_);
lean_dec_ref(v___y_4678_);
v___x_4690_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4689_);
return v___x_4690_;
}
v___jp_4691_:
{
if (v_kind_4672_ == 0)
{
uint8_t v___x_4695_; lean_object* v___x_4696_; 
v___x_4695_ = 0;
v___x_4696_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_4696_, 0, v___x_4695_);
lean_ctor_set_uint8(v___x_4696_, 1, v___x_4695_);
lean_ctor_set_uint8(v___x_4696_, 2, v___y_4693_);
v___y_4675_ = v___y_4692_;
v___y_4676_ = v___y_4694_;
v___y_4677_ = v___y_4693_;
v___y_4678_ = v___x_4696_;
goto v___jp_4674_;
}
else
{
uint8_t v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = 0;
v___x_4698_ = lean_alloc_ctor(1, 0, 5);
lean_ctor_set_uint8(v___x_4698_, 0, v___x_4697_);
lean_ctor_set_uint8(v___x_4698_, 1, v___x_4697_);
lean_ctor_set_uint8(v___x_4698_, 2, v___y_4693_);
lean_ctor_set_uint8(v___x_4698_, 3, v___x_4697_);
lean_ctor_set_uint8(v___x_4698_, 4, v___x_4697_);
v___y_4675_ = v___y_4692_;
v___y_4676_ = v___y_4694_;
v___y_4677_ = v___y_4693_;
v___y_4678_ = v___x_4698_;
goto v___jp_4674_;
}
}
v___jp_4700_:
{
uint8_t v___x_4704_; 
v___x_4704_ = 1;
if (v___y_4703_ == 0)
{
lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4705_ = lean_array_get_size(v___y_4702_);
v___x_4706_ = lean_nat_dec_lt(v___x_4699_, v___x_4705_);
if (v___x_4706_ == 0)
{
v___y_4692_ = v___y_4701_;
v___y_4693_ = v___x_4704_;
v___y_4694_ = v___y_4702_;
goto v___jp_4691_;
}
else
{
lean_object* v_v_4707_; lean_object* v___x_4708_; lean_object* v_xs_x27_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v_v_4707_ = lean_array_fget(v___y_4702_, v___x_4699_);
v___x_4708_ = lean_box(0);
v_xs_x27_4709_ = lean_array_fset(v___y_4702_, v___x_4699_, v___x_4708_);
v___x_4710_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4707_);
v___x_4711_ = lean_array_fset(v_xs_x27_4709_, v___x_4699_, v___x_4710_);
v___y_4692_ = v___y_4701_;
v___y_4693_ = v___x_4704_;
v___y_4694_ = v___x_4711_;
goto v___jp_4691_;
}
}
else
{
v___y_4692_ = v___y_4701_;
v___y_4693_ = v___x_4704_;
v___y_4694_ = v___y_4702_;
goto v___jp_4691_;
}
}
v___jp_4712_:
{
lean_object* v___x_4714_; lean_object* v_binderGroups_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; 
v___x_4714_ = lean_array_get_size(v_binderGroups_4669_);
v_binderGroups_4715_ = l_Array_filterMapM___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature_spec__1(v_binderGroups_4669_, v___x_4699_, v___x_4714_);
v___x_4716_ = lean_array_get_size(v___y_4713_);
v___x_4717_ = lean_unsigned_to_nat(1u);
v___x_4718_ = lean_nat_dec_le(v___x_4716_, v___x_4717_);
if (v___x_4718_ == 0)
{
v___y_4701_ = v_binderGroups_4715_;
v___y_4702_ = v___y_4713_;
v___y_4703_ = v___x_4718_;
goto v___jp_4700_;
}
else
{
uint8_t v___x_4719_; 
v___x_4719_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_type_4671_);
if (v___x_4719_ == 0)
{
v___y_4701_ = v_binderGroups_4715_;
v___y_4702_ = v___y_4713_;
v___y_4703_ = v___x_4719_;
goto v___jp_4700_;
}
else
{
uint8_t v___x_4720_; 
v___x_4720_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_typeAscriptionTk_4670_);
if (v___x_4720_ == 0)
{
v___y_4701_ = v_binderGroups_4715_;
v___y_4702_ = v___y_4713_;
v___y_4703_ = v___x_4720_;
goto v___jp_4700_;
}
else
{
lean_object* v___x_4721_; uint8_t v___x_4722_; 
v___x_4721_ = lean_array_get_size(v_binderGroups_4715_);
v___x_4722_ = lean_nat_dec_eq(v___x_4721_, v___x_4699_);
v___y_4701_ = v_binderGroups_4715_;
v___y_4702_ = v___y_4713_;
v___y_4703_ = v___x_4722_;
goto v___jp_4700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature___boxed(lean_object* v_lvals_4733_, lean_object* v_binderGroups_4734_, lean_object* v_typeAscriptionTk_4735_, lean_object* v_type_4736_, lean_object* v_kind_4737_, lean_object* v_lvalsLayout_4738_){
_start:
{
uint8_t v_kind_boxed_4739_; lean_object* v_res_4740_; 
v_kind_boxed_4739_ = lean_unbox(v_kind_4737_);
v_res_4740_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4733_, v_binderGroups_4734_, v_typeAscriptionTk_4735_, v_type_4736_, v_kind_boxed_4739_, v_lvalsLayout_4738_);
lean_dec_ref(v_binderGroups_4734_);
lean_dec_ref(v_lvals_4733_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0(lean_object* v_terms_4741_){
_start:
{
uint8_t v___x_4742_; lean_object* v___x_4743_; 
v___x_4742_ = 1;
v___x_4743_ = l_Lean_Fmt_Layouts_horizontalOrVertical(v_terms_4741_, v___x_4742_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___lam__0___boxed(lean_object* v_terms_4744_){
_start:
{
lean_object* v_res_4745_; 
v_res_4745_ = l_Lean_Fmt_Layouts_localSignature___lam__0(v_terms_4744_);
lean_dec_ref(v_terms_4744_);
return v_res_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature(lean_object* v_lvals_4747_, lean_object* v_binderGroups_4748_, lean_object* v_typeAscriptionTk_4749_, lean_object* v_type_4750_){
_start:
{
lean_object* v___f_4751_; uint8_t v___x_4752_; lean_object* v___x_4753_; 
v___f_4751_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4752_ = 0;
v___x_4753_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4747_, v_binderGroups_4748_, v_typeAscriptionTk_4749_, v_type_4750_, v___x_4752_, v___f_4751_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_localSignature___boxed(lean_object* v_lvals_4754_, lean_object* v_binderGroups_4755_, lean_object* v_typeAscriptionTk_4756_, lean_object* v_type_4757_){
_start:
{
lean_object* v_res_4758_; 
v_res_4758_ = l_Lean_Fmt_Layouts_localSignature(v_lvals_4754_, v_binderGroups_4755_, v_typeAscriptionTk_4756_, v_type_4757_);
lean_dec_ref(v_binderGroups_4755_);
lean_dec_ref(v_lvals_4754_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object* v_lvals_4759_, lean_object* v_binderGroups_4760_, lean_object* v_typeAscriptionTk_4761_, lean_object* v_type_4762_){
_start:
{
lean_object* v___f_4763_; uint8_t v___x_4764_; lean_object* v___x_4765_; 
v___f_4763_ = ((lean_object*)(l_Lean_Fmt_Layouts_localSignature___closed__0));
v___x_4764_ = 1;
v___x_4765_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lvals_4759_, v_binderGroups_4760_, v_typeAscriptionTk_4761_, v_type_4762_, v___x_4764_, v___f_4763_);
return v___x_4765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_globalSignature___boxed(lean_object* v_lvals_4766_, lean_object* v_binderGroups_4767_, lean_object* v_typeAscriptionTk_4768_, lean_object* v_type_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_Lean_Fmt_Layouts_globalSignature(v_lvals_4766_, v_binderGroups_4767_, v_typeAscriptionTk_4768_, v_type_4769_);
lean_dec_ref(v_binderGroups_4767_);
lean_dec_ref(v_lvals_4766_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object* v_signature_4771_, lean_object* v_separationTk_4772_, lean_object* v_body_4773_, uint8_t v_sticky_4774_){
_start:
{
lean_object* v___y_4776_; uint8_t v___y_4777_; lean_object* v___y_4778_; lean_object* v___y_4779_; uint8_t v___y_4780_; uint8_t v___y_4784_; lean_object* v___y_4785_; uint8_t v___y_4809_; uint8_t v___x_4825_; 
v___x_4825_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_separationTk_4772_);
if (v___x_4825_ == 0)
{
v___y_4809_ = v___x_4825_;
goto v___jp_4808_;
}
else
{
uint8_t v___x_4826_; 
v___x_4826_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4773_);
v___y_4809_ = v___x_4826_;
goto v___jp_4808_;
}
v___jp_4775_:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
lean_inc_ref(v___y_4776_);
v___x_4781_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v___y_4778_, v___y_4776_, v_body_4773_, v___y_4780_);
v___x_4782_ = l_Lean_Fmt_TaggedDoc_sticky(v___y_4779_, v___x_4781_, v___y_4777_);
return v___x_4782_;
}
v___jp_4783_:
{
lean_object* v_doc_4786_; 
v_doc_4786_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___y_4785_);
if (v_sticky_4774_ == 0)
{
lean_dec_ref(v_body_4773_);
lean_dec_ref(v_separationTk_4772_);
lean_dec_ref(v_signature_4771_);
return v_doc_4786_;
}
else
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v_lhs_4798_; lean_object* v___x_4799_; 
v___x_4787_ = l_Lean_Fmt_TaggedDoc_flattened(v_signature_4771_);
v___x_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4787_);
v___x_4789_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4790_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4788_, v___x_4789_);
v___x_4791_ = lean_box(0);
v___x_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4792_, 0, v_separationTk_4772_);
v___x_4793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4791_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
lean_ctor_set(v___x_4793_, 2, v___x_4791_);
v___x_4794_ = lean_unsigned_to_nat(2u);
v___x_4795_ = lean_mk_empty_array_with_capacity(v___x_4794_);
v___x_4796_ = lean_array_push(v___x_4795_, v___x_4790_);
v___x_4797_ = lean_array_push(v___x_4796_, v___x_4793_);
v_lhs_4798_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4797_);
lean_dec_ref(v___x_4797_);
lean_inc_ref(v_body_4773_);
v___x_4799_ = l_Lean_Fmt_TaggedDoc_getSticky_x3f(v_body_4773_);
if (lean_obj_tag(v___x_4799_) == 1)
{
lean_object* v_val_4800_; uint8_t v_kind_4801_; lean_object* v___x_4802_; 
v_val_4800_ = lean_ctor_get(v___x_4799_, 0);
lean_inc(v_val_4800_);
lean_dec_ref_known(v___x_4799_, 1);
v_kind_4801_ = lean_ctor_get_uint8(v_val_4800_, sizeof(void*)*1);
lean_dec(v_val_4800_);
v___x_4802_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
if (v_kind_4801_ == 1)
{
uint8_t v___x_4803_; 
v___x_4803_ = 0;
v___y_4776_ = v___x_4802_;
v___y_4777_ = v_kind_4801_;
v___y_4778_ = v_lhs_4798_;
v___y_4779_ = v_doc_4786_;
v___y_4780_ = v___x_4803_;
goto v___jp_4775_;
}
else
{
v___y_4776_ = v___x_4802_;
v___y_4777_ = v_kind_4801_;
v___y_4778_ = v_lhs_4798_;
v___y_4779_ = v_doc_4786_;
v___y_4780_ = v_sticky_4774_;
goto v___jp_4775_;
}
}
else
{
lean_object* v___x_4804_; lean_object* v___x_4805_; uint8_t v___x_4806_; lean_object* v___x_4807_; 
lean_dec(v___x_4799_);
v___x_4804_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_4805_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4798_, v___x_4804_, v_body_4773_, v___y_4784_);
v___x_4806_ = 0;
v___x_4807_ = l_Lean_Fmt_TaggedDoc_sticky(v_doc_4786_, v___x_4805_, v___x_4806_);
return v___x_4807_;
}
}
}
v___jp_4808_:
{
uint8_t v___x_4810_; 
v___x_4810_ = 1;
if (v___y_4809_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v_lhs_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
lean_inc_ref(v_signature_4771_);
v___x_4811_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4771_);
v___x_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
v___x_4813_ = lean_obj_once(&l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0, &l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0_once, _init_l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_applicationWithSomeFilled_dense___closed__0);
v___x_4814_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4812_, v___x_4813_);
v___x_4815_ = lean_box(0);
lean_inc_ref(v_separationTk_4772_);
v___x_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4816_, 0, v_separationTk_4772_);
v___x_4817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4815_);
lean_ctor_set(v___x_4817_, 1, v___x_4816_);
lean_ctor_set(v___x_4817_, 2, v___x_4815_);
v___x_4818_ = lean_unsigned_to_nat(2u);
v___x_4819_ = lean_mk_empty_array_with_capacity(v___x_4818_);
v___x_4820_ = lean_array_push(v___x_4819_, v___x_4814_);
v___x_4821_ = lean_array_push(v___x_4820_, v___x_4817_);
v_lhs_4822_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4821_);
lean_dec_ref(v___x_4821_);
v___x_4823_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
lean_inc_ref(v_body_4773_);
v___x_4824_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4822_, v___x_4823_, v_body_4773_, v___x_4810_);
v___y_4784_ = v___x_4810_;
v___y_4785_ = v___x_4824_;
goto v___jp_4783_;
}
else
{
lean_inc_ref(v_signature_4771_);
v___y_4784_ = v___x_4810_;
v___y_4785_ = v_signature_4771_;
goto v___jp_4783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration___boxed(lean_object* v_signature_4827_, lean_object* v_separationTk_4828_, lean_object* v_body_4829_, lean_object* v_sticky_4830_){
_start:
{
uint8_t v_sticky_boxed_4831_; lean_object* v_res_4832_; 
v_sticky_boxed_4831_ = lean_unbox(v_sticky_4830_);
v_res_4832_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_signature_4827_, v_separationTk_4828_, v_body_4829_, v_sticky_boxed_4831_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_matchDeclaration(lean_object* v_signature_4833_, lean_object* v_matchAlts_4834_){
_start:
{
lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4835_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4833_);
v___x_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4835_);
v___x_4837_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4838_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4836_, v___x_4837_);
v___x_4839_ = lean_box(0);
v___x_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4840_, 0, v_matchAlts_4834_);
v___x_4841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4839_);
lean_ctor_set(v___x_4841_, 1, v___x_4840_);
lean_ctor_set(v___x_4841_, 2, v___x_4839_);
v___x_4842_ = lean_unsigned_to_nat(2u);
v___x_4843_ = lean_mk_empty_array_with_capacity(v___x_4842_);
v___x_4844_ = lean_array_push(v___x_4843_, v___x_4838_);
v___x_4845_ = lean_array_push(v___x_4844_, v___x_4841_);
v___x_4846_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4845_);
lean_dec_ref(v___x_4845_);
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_whereDeclaration(lean_object* v_signature_4847_, lean_object* v_whereTk_4848_, lean_object* v_body_4849_){
_start:
{
uint8_t v___x_4850_; 
v___x_4850_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_body_4849_);
if (v___x_4850_ == 0)
{
uint8_t v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v_lhs_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4851_ = 1;
v___x_4852_ = l_Lean_Fmt_TaggedDoc_hardNested(v_signature_4847_);
v___x_4853_ = lean_unsigned_to_nat(2u);
v___x_4854_ = lean_mk_empty_array_with_capacity(v___x_4853_);
v___x_4855_ = lean_array_push(v___x_4854_, v___x_4852_);
v___x_4856_ = lean_array_push(v___x_4855_, v_whereTk_4848_);
v_lhs_4857_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4856_);
lean_dec_ref(v___x_4856_);
v___x_4858_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSepArray___closed__0);
v___x_4859_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_lhs_4857_, v___x_4858_, v_body_4849_, v___x_4851_);
v___x_4860_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4859_);
return v___x_4860_;
}
else
{
lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
lean_dec_ref(v_body_4849_);
v___x_4861_ = lean_unsigned_to_nat(2u);
v___x_4862_ = lean_mk_empty_array_with_capacity(v___x_4861_);
v___x_4863_ = lean_array_push(v___x_4862_, v_signature_4847_);
v___x_4864_ = lean_array_push(v___x_4863_, v_whereTk_4848_);
v___x_4865_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_4864_);
lean_dec_ref(v___x_4864_);
return v___x_4865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder(lean_object* v_lbs_4867_, lean_object* v_lhses_4868_, lean_object* v_subBinderGroups_4869_, lean_object* v_typeAscriptionTk_x3f_4870_, lean_object* v_type_x3f_4871_, lean_object* v_colonEqTk_x3f_4872_, lean_object* v_default_x3f_4873_, lean_object* v_rbs_4874_, uint8_t v_kind_4875_){
_start:
{
lean_object* v_lbs_4876_; lean_object* v___x_4877_; lean_object* v_binderSignature_4878_; uint8_t v___x_4879_; lean_object* v_simpleBinder_4880_; lean_object* v_rbs_4881_; lean_object* v___x_4882_; 
v_lbs_4876_ = l_Lean_Fmt_Layouts_atomic(v_lbs_4867_);
v___x_4877_ = ((lean_object*)(l_Lean_Fmt_Layouts_binder___closed__0));
v_binderSignature_4878_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_signature(v_lhses_4868_, v_subBinderGroups_4869_, v_typeAscriptionTk_x3f_4870_, v_type_x3f_4871_, v_kind_4875_, v___x_4877_);
v___x_4879_ = 0;
v_simpleBinder_4880_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v_binderSignature_4878_, v_colonEqTk_x3f_4872_, v_default_x3f_4873_, v___x_4879_);
v_rbs_4881_ = l_Lean_Fmt_Layouts_atomic(v_rbs_4874_);
v___x_4882_ = l_Lean_Fmt_Layouts_parens(v_lbs_4876_, v_simpleBinder_4880_, v_rbs_4881_);
return v___x_4882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_binder___boxed(lean_object* v_lbs_4883_, lean_object* v_lhses_4884_, lean_object* v_subBinderGroups_4885_, lean_object* v_typeAscriptionTk_x3f_4886_, lean_object* v_type_x3f_4887_, lean_object* v_colonEqTk_x3f_4888_, lean_object* v_default_x3f_4889_, lean_object* v_rbs_4890_, lean_object* v_kind_4891_){
_start:
{
uint8_t v_kind_boxed_4892_; lean_object* v_res_4893_; 
v_kind_boxed_4892_ = lean_unbox(v_kind_4891_);
v_res_4893_ = l_Lean_Fmt_Layouts_binder(v_lbs_4883_, v_lhses_4884_, v_subBinderGroups_4885_, v_typeAscriptionTk_x3f_4886_, v_type_x3f_4887_, v_colonEqTk_x3f_4888_, v_default_x3f_4889_, v_rbs_4890_, v_kind_boxed_4892_);
lean_dec_ref(v_rbs_4890_);
lean_dec_ref(v_subBinderGroups_4885_);
lean_dec_ref(v_lhses_4884_);
lean_dec_ref(v_lbs_4883_);
return v_res_4893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl(lean_object* v_keywordTk_4897_, lean_object* v_config_4898_, lean_object* v_decl_4899_, uint8_t v_format_4900_){
_start:
{
lean_object* v___f_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v_signature_4907_; lean_object* v___y_4909_; 
v___f_4901_ = ((lean_object*)(l_Lean_Fmt_Layouts_keywordSeparated___closed__0));
v___x_4902_ = lean_unsigned_to_nat(2u);
v___x_4903_ = lean_mk_empty_array_with_capacity(v___x_4902_);
lean_inc_ref(v___x_4903_);
v___x_4904_ = lean_array_push(v___x_4903_, v_keywordTk_4897_);
v___x_4905_ = lean_array_push(v___x_4904_, v_config_4898_);
v___x_4906_ = ((lean_object*)(l_Lean_Fmt_Layouts_letDecl___closed__0));
v_signature_4907_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_4905_, v___x_4906_);
if (v_format_4900_ == 0)
{
lean_object* v___x_4921_; 
v___x_4921_ = l_Lean_Fmt_TaggedDoc_space;
v___y_4909_ = v___x_4921_;
goto v___jp_4908_;
}
else
{
lean_object* v___x_4922_; 
v___x_4922_ = l_Lean_Fmt_TaggedDoc_nl;
v___y_4909_ = v___x_4922_;
goto v___jp_4908_;
}
v___jp_4908_:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4910_, 0, v_signature_4907_);
lean_inc_ref(v___y_4909_);
v___x_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4911_, 0, v___y_4909_);
lean_ctor_set(v___x_4911_, 1, v___f_4901_);
v___x_4912_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_4910_, v___x_4911_);
v___x_4913_ = lean_box(0);
v___x_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4914_, 0, v_decl_4899_);
v___x_4915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4913_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
lean_ctor_set(v___x_4915_, 2, v___x_4913_);
v___x_4916_ = lean_array_push(v___x_4903_, v___x_4912_);
v___x_4917_ = lean_array_push(v___x_4916_, v___x_4915_);
v___x_4918_ = l_Lean_Fmt_TaggedDoc_combine(v___x_4917_);
lean_dec_ref(v___x_4917_);
v___x_4919_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v___x_4918_);
v___x_4920_ = l_Lean_Fmt_TaggedDoc_nested(v___x_4919_);
return v___x_4920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_letDecl___boxed(lean_object* v_keywordTk_4923_, lean_object* v_config_4924_, lean_object* v_decl_4925_, lean_object* v_format_4926_){
_start:
{
uint8_t v_format_boxed_4927_; lean_object* v_res_4928_; 
v_format_boxed_4927_ = lean_unbox(v_format_4926_);
v_res_4928_ = l_Lean_Fmt_Layouts_letDecl(v_keywordTk_4923_, v_config_4924_, v_decl_4925_, v_format_boxed_4927_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(size_t v_sz_4929_, size_t v_i_4930_, lean_object* v_bs_4931_){
_start:
{
uint8_t v___x_4932_; 
v___x_4932_ = lean_usize_dec_lt(v_i_4930_, v_sz_4929_);
if (v___x_4932_ == 0)
{
return v_bs_4931_;
}
else
{
lean_object* v_v_4933_; lean_object* v_quantifier_4934_; lean_object* v_binderGroups_4935_; lean_object* v_typeAscriptionTk_x3f_4936_; lean_object* v_type_x3f_4937_; lean_object* v_separationTk_4938_; lean_object* v___x_4939_; lean_object* v_bs_x27_4940_; lean_object* v___x_4941_; lean_object* v_signature_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; uint8_t v___x_4948_; lean_object* v___x_4949_; size_t v___x_4950_; size_t v___x_4951_; lean_object* v___x_4952_; 
v_v_4933_ = lean_array_uget_borrowed(v_bs_4931_, v_i_4930_);
v_quantifier_4934_ = lean_ctor_get(v_v_4933_, 0);
lean_inc_ref(v_quantifier_4934_);
v_binderGroups_4935_ = lean_ctor_get(v_v_4933_, 1);
lean_inc_ref(v_binderGroups_4935_);
v_typeAscriptionTk_x3f_4936_ = lean_ctor_get(v_v_4933_, 2);
lean_inc_ref(v_typeAscriptionTk_x3f_4936_);
v_type_x3f_4937_ = lean_ctor_get(v_v_4933_, 3);
lean_inc_ref(v_type_x3f_4937_);
v_separationTk_4938_ = lean_ctor_get(v_v_4933_, 4);
lean_inc_ref(v_separationTk_4938_);
v___x_4939_ = lean_unsigned_to_nat(0u);
v_bs_x27_4940_ = lean_array_uset(v_bs_4931_, v_i_4930_, v___x_4939_);
v___x_4941_ = ((lean_object*)(l_Lean_Fmt_Layouts_array___closed__0));
v_signature_4942_ = l_Lean_Fmt_Layouts_localSignature(v___x_4941_, v_binderGroups_4935_, v_typeAscriptionTk_x3f_4936_, v_type_x3f_4937_);
lean_dec_ref(v_binderGroups_4935_);
v___x_4943_ = lean_unsigned_to_nat(2u);
v___x_4944_ = lean_mk_empty_array_with_capacity(v___x_4943_);
v___x_4945_ = lean_array_push(v___x_4944_, v_signature_4942_);
v___x_4946_ = lean_array_push(v___x_4945_, v_separationTk_4938_);
v___x_4947_ = l_Lean_Fmt_Layouts_atomic(v___x_4946_);
lean_dec_ref(v___x_4946_);
v___x_4948_ = 2;
v___x_4949_ = l_Lean_Fmt_Layouts_prefixOperator(v_quantifier_4934_, v___x_4947_, v___x_4948_);
v___x_4950_ = ((size_t)1ULL);
v___x_4951_ = lean_usize_add(v_i_4930_, v___x_4950_);
v___x_4952_ = lean_array_uset(v_bs_x27_4940_, v_i_4930_, v___x_4949_);
v_i_4930_ = v___x_4951_;
v_bs_4931_ = v___x_4952_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0___boxed(lean_object* v_sz_4954_, lean_object* v_i_4955_, lean_object* v_bs_4956_){
_start:
{
size_t v_sz_boxed_4957_; size_t v_i_boxed_4958_; lean_object* v_res_4959_; 
v_sz_boxed_4957_ = lean_unbox_usize(v_sz_4954_);
lean_dec(v_sz_4954_);
v_i_boxed_4958_ = lean_unbox_usize(v_i_4955_);
lean_dec(v_i_4955_);
v_res_4959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_boxed_4957_, v_i_boxed_4958_, v_bs_4956_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(size_t v_sz_4960_, size_t v_i_4961_, lean_object* v_bs_4962_){
_start:
{
uint8_t v___x_4963_; 
v___x_4963_ = lean_usize_dec_lt(v_i_4961_, v_sz_4960_);
if (v___x_4963_ == 0)
{
return v_bs_4962_;
}
else
{
lean_object* v_v_4964_; lean_object* v___x_4965_; lean_object* v_bs_x27_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; size_t v___x_4969_; size_t v___x_4970_; lean_object* v___x_4971_; 
v_v_4964_ = lean_array_uget(v_bs_4962_, v_i_4961_);
v___x_4965_ = lean_unsigned_to_nat(0u);
v_bs_x27_4966_ = lean_array_uset(v_bs_4962_, v_i_4961_, v___x_4965_);
v___x_4967_ = l_Lean_Fmt_TaggedDoc_hardNested(v_v_4964_);
v___x_4968_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
lean_ctor_set_uint8(v___x_4968_, sizeof(void*)*1, v___x_4963_);
v___x_4969_ = ((size_t)1ULL);
v___x_4970_ = lean_usize_add(v_i_4961_, v___x_4969_);
v___x_4971_ = lean_array_uset(v_bs_x27_4966_, v_i_4961_, v___x_4968_);
v_i_4961_ = v___x_4970_;
v_bs_4962_ = v___x_4971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1___boxed(lean_object* v_sz_4973_, lean_object* v_i_4974_, lean_object* v_bs_4975_){
_start:
{
size_t v_sz_boxed_4976_; size_t v_i_boxed_4977_; lean_object* v_res_4978_; 
v_sz_boxed_4976_ = lean_unbox_usize(v_sz_4973_);
lean_dec(v_sz_4973_);
v_i_boxed_4977_ = lean_unbox_usize(v_i_4974_);
lean_dec(v_i_4974_);
v_res_4978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_boxed_4976_, v_i_boxed_4977_, v_bs_4975_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_quantified(lean_object* v_quantifierHeads_4979_, lean_object* v_body_4980_){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; 
v___x_4981_ = lean_array_get_size(v_quantifierHeads_4979_);
v___x_4982_ = lean_unsigned_to_nat(0u);
v___x_4983_ = lean_nat_dec_eq(v___x_4981_, v___x_4982_);
if (v___x_4983_ == 0)
{
size_t v_sz_4984_; size_t v___x_4985_; lean_object* v_quantifierHeads_4986_; size_t v_sz_4987_; lean_object* v_quantifierHeads_4988_; lean_object* v___x_4989_; lean_object* v_components_4990_; lean_object* v___x_4991_; lean_object* v_quantifiers_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v_sz_4984_ = lean_array_size(v_quantifierHeads_4979_);
v___x_4985_ = ((size_t)0ULL);
v_quantifierHeads_4986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__0(v_sz_4984_, v___x_4985_, v_quantifierHeads_4979_);
v_sz_4987_ = lean_array_size(v_quantifierHeads_4986_);
v_quantifierHeads_4988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_quantified_spec__1(v_sz_4987_, v___x_4985_, v_quantifierHeads_4986_);
v___x_4989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4989_, 0, v_body_4980_);
lean_ctor_set_uint8(v___x_4989_, sizeof(void*)*1, v___x_4983_);
v_components_4990_ = lean_array_push(v_quantifierHeads_4988_, v___x_4989_);
v___x_4991_ = ((lean_object*)(l_Lean_Fmt_Layouts_infixOperator___closed__2));
v_quantifiers_4992_ = l_Lean_Fmt_TaggedDoc_fillSomeUsingSpaceWrapping(v_components_4990_, v___x_4991_);
v___x_4993_ = l_Lean_Fmt_TaggedDoc_maybeFlattened(v_quantifiers_4992_);
v___x_4994_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_4993_);
return v___x_4994_;
}
else
{
lean_dec_ref(v_quantifierHeads_4979_);
return v_body_4980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_subtype(lean_object* v_lbTk_4998_, lean_object* v_lhs_4999_, lean_object* v_sepTk_5000_, lean_object* v_rhs_5001_, lean_object* v_rbTk_5002_, lean_object* v_format_5003_){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v_body_5011_; lean_object* v___x_5012_; 
v___x_5004_ = lean_unsigned_to_nat(3u);
v___x_5005_ = lean_mk_empty_array_with_capacity(v___x_5004_);
v___x_5006_ = lean_array_push(v___x_5005_, v_lhs_4999_);
v___x_5007_ = lean_array_push(v___x_5006_, v_sepTk_5000_);
v___x_5008_ = lean_array_push(v___x_5007_, v_rhs_5001_);
v___x_5009_ = ((lean_object*)(l_Lean_Fmt_Layouts_subtype___closed__0));
v___x_5010_ = l_Lean_Fmt_Layouts_infixOperator(v___x_5008_, v___x_5009_);
v_body_5011_ = l_Lean_Fmt_TaggedDoc_pseudoAligned(v___x_5010_);
v___x_5012_ = l_Lean_Fmt_Layouts_bracketed(v_lbTk_4998_, v_body_5011_, v_rbTk_5002_, v_format_5003_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(lean_object* v_tk_5013_, lean_object* v_block_5014_, uint8_t v_allowFlattening_5015_){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = lean_obj_once(&l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0, &l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0_once, _init_l_Lean_Fmt_Layouts_keywordPrefixedSeq___closed__0);
v___x_5017_ = l_Lean_Fmt_TaggedDoc_stickyCombine(v_tk_5013_, v___x_5016_, v_block_5014_, v_allowFlattening_5015_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken___boxed(lean_object* v_tk_5018_, lean_object* v_block_5019_, lean_object* v_allowFlattening_5020_){
_start:
{
uint8_t v_allowFlattening_boxed_5021_; lean_object* v_res_5022_; 
v_allowFlattening_boxed_5021_ = lean_unbox(v_allowFlattening_5020_);
v_res_5022_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_tk_5018_, v_block_5019_, v_allowFlattening_boxed_5021_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(uint8_t v_allowFlattening_5023_, size_t v_sz_5024_, size_t v_i_5025_, lean_object* v_bs_5026_){
_start:
{
uint8_t v___x_5027_; 
v___x_5027_ = lean_usize_dec_lt(v_i_5025_, v_sz_5024_);
if (v___x_5027_ == 0)
{
return v_bs_5026_;
}
else
{
lean_object* v_v_5028_; lean_object* v_elseTk_5029_; lean_object* v_ifTk_5030_; lean_object* v_cond_5031_; lean_object* v_thenTk_5032_; lean_object* v_thenBlock_5033_; lean_object* v___x_5034_; lean_object* v_bs_x27_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v_tk_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; lean_object* v___x_5044_; lean_object* v_head_5045_; lean_object* v_then_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v_trailingThen_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v_leadingThen_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; size_t v___x_5066_; size_t v___x_5067_; lean_object* v___x_5068_; 
v_v_5028_ = lean_array_uget_borrowed(v_bs_5026_, v_i_5025_);
v_elseTk_5029_ = lean_ctor_get(v_v_5028_, 0);
lean_inc_ref(v_elseTk_5029_);
v_ifTk_5030_ = lean_ctor_get(v_v_5028_, 1);
lean_inc_ref(v_ifTk_5030_);
v_cond_5031_ = lean_ctor_get(v_v_5028_, 2);
lean_inc_ref(v_cond_5031_);
v_thenTk_5032_ = lean_ctor_get(v_v_5028_, 3);
lean_inc_ref(v_thenTk_5032_);
v_thenBlock_5033_ = lean_ctor_get(v_v_5028_, 4);
lean_inc_ref(v_thenBlock_5033_);
v___x_5034_ = lean_unsigned_to_nat(0u);
v_bs_x27_5035_ = lean_array_uset(v_bs_5026_, v_i_5025_, v___x_5034_);
v___x_5036_ = lean_unsigned_to_nat(2u);
v___x_5037_ = lean_mk_empty_array_with_capacity(v___x_5036_);
lean_inc_ref_n(v___x_5037_, 4);
v___x_5038_ = lean_array_push(v___x_5037_, v_elseTk_5029_);
v___x_5039_ = lean_array_push(v___x_5038_, v_ifTk_5030_);
v_tk_5040_ = l_Lean_Fmt_Layouts_spacedAtomic(v___x_5039_);
lean_dec_ref(v___x_5039_);
v___x_5041_ = lean_array_push(v___x_5037_, v_tk_5040_);
v___x_5042_ = lean_array_push(v___x_5041_, v_cond_5031_);
v___x_5043_ = 0;
v___x_5044_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_5044_, 0, v___x_5027_);
lean_ctor_set_uint8(v___x_5044_, 1, v___x_5043_);
lean_ctor_set_uint8(v___x_5044_, 2, v___x_5043_);
lean_ctor_set_uint8(v___x_5044_, 3, v___x_5043_);
v_head_5045_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_5042_, v___x_5044_);
v_then_5046_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_thenTk_5032_, v_thenBlock_5033_, v_allowFlattening_5023_);
lean_inc_ref(v_head_5045_);
v___x_5047_ = l_Lean_Fmt_TaggedDoc_flattened(v_head_5045_);
v___x_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5048_, 0, v___x_5047_);
v___x_5049_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__1___closed__1);
v___x_5050_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_5048_, v___x_5049_);
v___x_5051_ = lean_box(0);
v___x_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5052_, 0, v_then_5046_);
v___x_5053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5051_);
lean_ctor_set(v___x_5053_, 1, v___x_5052_);
lean_ctor_set(v___x_5053_, 2, v___x_5051_);
v___x_5054_ = lean_array_push(v___x_5037_, v___x_5050_);
lean_inc_ref(v___x_5053_);
v___x_5055_ = lean_array_push(v___x_5054_, v___x_5053_);
v_trailingThen_5056_ = l_Lean_Fmt_TaggedDoc_combine(v___x_5055_);
lean_dec_ref(v___x_5055_);
v___x_5057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5057_, 0, v_head_5045_);
v___x_5058_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4___closed__0);
v___x_5059_ = l_Lean_Fmt_TaggedDoc_Component_withSepAfter(v___x_5057_, v___x_5058_);
v___x_5060_ = lean_array_push(v___x_5037_, v___x_5059_);
v___x_5061_ = lean_array_push(v___x_5060_, v___x_5053_);
v_leadingThen_5062_ = l_Lean_Fmt_TaggedDoc_combine(v___x_5061_);
lean_dec_ref(v___x_5061_);
v___x_5063_ = lean_array_push(v___x_5037_, v_trailingThen_5056_);
v___x_5064_ = lean_array_push(v___x_5063_, v_leadingThen_5062_);
v___x_5065_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_5064_);
v___x_5066_ = ((size_t)1ULL);
v___x_5067_ = lean_usize_add(v_i_5025_, v___x_5066_);
v___x_5068_ = lean_array_uset(v_bs_x27_5035_, v_i_5025_, v___x_5065_);
v_i_5025_ = v___x_5067_;
v_bs_5026_ = v___x_5068_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0___boxed(lean_object* v_allowFlattening_5070_, lean_object* v_sz_5071_, lean_object* v_i_5072_, lean_object* v_bs_5073_){
_start:
{
uint8_t v_allowFlattening_boxed_5074_; size_t v_sz_boxed_5075_; size_t v_i_boxed_5076_; lean_object* v_res_5077_; 
v_allowFlattening_boxed_5074_ = lean_unbox(v_allowFlattening_5070_);
v_sz_boxed_5075_ = lean_unbox_usize(v_sz_5071_);
lean_dec(v_sz_5071_);
v_i_boxed_5076_ = lean_unbox_usize(v_i_5072_);
lean_dec(v_i_5072_);
v_res_5077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_boxed_5074_, v_sz_boxed_5075_, v_i_boxed_5076_, v_bs_5073_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(lean_object* v_elseIfs_5078_, lean_object* v_elseTk_5079_, lean_object* v_elseBlock_5080_, uint8_t v_allowFlattening_5081_){
_start:
{
size_t v_sz_5082_; size_t v___x_5083_; lean_object* v_elseIfs_5084_; lean_object* v_else_5085_; lean_object* v_blocks_5086_; size_t v_sz_5087_; lean_object* v_blocks_5088_; lean_object* v_conditional_5089_; lean_object* v___x_5090_; 
v_sz_5082_ = lean_array_size(v_elseIfs_5078_);
v___x_5083_ = ((size_t)0ULL);
v_elseIfs_5084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk_spec__0(v_allowFlattening_5081_, v_sz_5082_, v___x_5083_, v_elseIfs_5078_);
v_else_5085_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_attachBlockToToken(v_elseTk_5079_, v_elseBlock_5080_, v_allowFlattening_5081_);
v_blocks_5086_ = lean_array_push(v_elseIfs_5084_, v_else_5085_);
v_sz_5087_ = lean_array_size(v_blocks_5086_);
v_blocks_5088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Layouts_array_spec__4(v_sz_5087_, v___x_5083_, v_blocks_5086_);
v_conditional_5089_ = l_Lean_Fmt_TaggedDoc_combine(v_blocks_5088_);
lean_dec_ref(v_blocks_5088_);
v___x_5090_ = l_Lean_Fmt_TaggedDoc_aligned(v_conditional_5089_);
return v___x_5090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk___boxed(lean_object* v_elseIfs_5091_, lean_object* v_elseTk_5092_, lean_object* v_elseBlock_5093_, lean_object* v_allowFlattening_5094_){
_start:
{
uint8_t v_allowFlattening_boxed_5095_; lean_object* v_res_5096_; 
v_allowFlattening_boxed_5095_ = lean_unbox(v_allowFlattening_5094_);
v_res_5096_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5091_, v_elseTk_5092_, v_elseBlock_5093_, v_allowFlattening_boxed_5095_);
return v_res_5096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(lean_object* v_as_5097_, size_t v_i_5098_, size_t v_stop_5099_, lean_object* v_b_5100_){
_start:
{
lean_object* v___y_5102_; uint8_t v___x_5106_; 
v___x_5106_ = lean_usize_dec_eq(v_i_5098_, v_stop_5099_);
if (v___x_5106_ == 0)
{
lean_object* v___x_5107_; uint8_t v___y_5109_; lean_object* v_elseTk_5120_; lean_object* v_ifTk_5121_; uint8_t v___x_5122_; 
v___x_5107_ = lean_array_uget_borrowed(v_as_5097_, v_i_5098_);
v_elseTk_5120_ = lean_ctor_get(v___x_5107_, 0);
v_ifTk_5121_ = lean_ctor_get(v___x_5107_, 1);
v___x_5122_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_elseTk_5120_);
if (v___x_5122_ == 0)
{
v___y_5109_ = v___x_5122_;
goto v___jp_5108_;
}
else
{
uint8_t v___x_5123_; 
v___x_5123_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_ifTk_5121_);
v___y_5109_ = v___x_5123_;
goto v___jp_5108_;
}
v___jp_5108_:
{
if (v___y_5109_ == 0)
{
lean_object* v___x_5110_; 
lean_inc(v___x_5107_);
v___x_5110_ = lean_array_push(v_b_5100_, v___x_5107_);
v___y_5102_ = v___x_5110_;
goto v___jp_5101_;
}
else
{
lean_object* v_cond_5111_; lean_object* v_thenTk_5112_; lean_object* v_thenBlock_5113_; uint8_t v___x_5114_; 
v_cond_5111_ = lean_ctor_get(v___x_5107_, 2);
v_thenTk_5112_ = lean_ctor_get(v___x_5107_, 3);
v_thenBlock_5113_ = lean_ctor_get(v___x_5107_, 4);
v___x_5114_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_cond_5111_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5115_; 
lean_inc(v___x_5107_);
v___x_5115_ = lean_array_push(v_b_5100_, v___x_5107_);
v___y_5102_ = v___x_5115_;
goto v___jp_5101_;
}
else
{
uint8_t v___x_5116_; 
v___x_5116_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenTk_5112_);
if (v___x_5116_ == 0)
{
lean_object* v___x_5117_; 
lean_inc(v___x_5107_);
v___x_5117_ = lean_array_push(v_b_5100_, v___x_5107_);
v___y_5102_ = v___x_5117_;
goto v___jp_5101_;
}
else
{
uint8_t v___x_5118_; 
v___x_5118_ = l_Lean_Fmt_TaggedDoc_isAlwaysEmpty(v_thenBlock_5113_);
if (v___x_5118_ == 0)
{
lean_object* v___x_5119_; 
lean_inc(v___x_5107_);
v___x_5119_ = lean_array_push(v_b_5100_, v___x_5107_);
v___y_5102_ = v___x_5119_;
goto v___jp_5101_;
}
else
{
v___y_5102_ = v_b_5100_;
goto v___jp_5101_;
}
}
}
}
}
}
else
{
return v_b_5100_;
}
v___jp_5101_:
{
size_t v___x_5103_; size_t v___x_5104_; 
v___x_5103_ = ((size_t)1ULL);
v___x_5104_ = lean_usize_add(v_i_5098_, v___x_5103_);
v_i_5098_ = v___x_5104_;
v_b_5100_ = v___y_5102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0___boxed(lean_object* v_as_5124_, lean_object* v_i_5125_, lean_object* v_stop_5126_, lean_object* v_b_5127_){
_start:
{
size_t v_i_boxed_5128_; size_t v_stop_boxed_5129_; lean_object* v_res_5130_; 
v_i_boxed_5128_ = lean_unbox_usize(v_i_5125_);
lean_dec(v_i_5125_);
v_stop_boxed_5129_ = lean_unbox_usize(v_stop_5126_);
lean_dec(v_stop_5126_);
v_res_5130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_as_5124_, v_i_boxed_5128_, v_stop_boxed_5129_, v_b_5127_);
lean_dec_ref(v_as_5124_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional(lean_object* v_ifTk_5133_, lean_object* v_cond_5134_, lean_object* v_thenTk_5135_, lean_object* v_thenBlock_5136_, lean_object* v_elseIfs_5137_, lean_object* v_elseTk_5138_, lean_object* v_elseBlock_5139_, uint8_t v_allowFlattening_5140_){
_start:
{
lean_object* v___y_5142_; uint8_t v___y_5143_; lean_object* v___y_5162_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; uint8_t v___x_5169_; 
v___x_5166_ = lean_unsigned_to_nat(0u);
v___x_5167_ = lean_array_get_size(v_elseIfs_5137_);
v___x_5168_ = ((lean_object*)(l_Lean_Fmt_Layouts_conditional___closed__0));
v___x_5169_ = lean_nat_dec_lt(v___x_5166_, v___x_5167_);
if (v___x_5169_ == 0)
{
v___y_5162_ = v___x_5168_;
goto v___jp_5161_;
}
else
{
uint8_t v___x_5170_; 
v___x_5170_ = lean_nat_dec_le(v___x_5167_, v___x_5167_);
if (v___x_5170_ == 0)
{
if (v___x_5169_ == 0)
{
v___y_5162_ = v___x_5168_;
goto v___jp_5161_;
}
else
{
size_t v___x_5171_; size_t v___x_5172_; lean_object* v___x_5173_; 
v___x_5171_ = ((size_t)0ULL);
v___x_5172_ = lean_usize_of_nat(v___x_5167_);
v___x_5173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_5137_, v___x_5171_, v___x_5172_, v___x_5168_);
v___y_5162_ = v___x_5173_;
goto v___jp_5161_;
}
}
else
{
size_t v___x_5174_; size_t v___x_5175_; lean_object* v___x_5176_; 
v___x_5174_ = ((size_t)0ULL);
v___x_5175_ = lean_usize_of_nat(v___x_5167_);
v___x_5176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Layouts_conditional_spec__0(v_elseIfs_5137_, v___x_5174_, v___x_5175_, v___x_5168_);
v___y_5162_ = v___x_5176_;
goto v___jp_5161_;
}
}
v___jp_5141_:
{
lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v_elseIfs_5149_; 
v___x_5144_ = l_Lean_Fmt_TaggedDoc_empty;
v___x_5145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5145_, 0, v___x_5144_);
lean_ctor_set(v___x_5145_, 1, v_ifTk_5133_);
lean_ctor_set(v___x_5145_, 2, v_cond_5134_);
lean_ctor_set(v___x_5145_, 3, v_thenTk_5135_);
lean_ctor_set(v___x_5145_, 4, v_thenBlock_5136_);
v___x_5146_ = lean_unsigned_to_nat(1u);
v___x_5147_ = lean_mk_empty_array_with_capacity(v___x_5146_);
v___x_5148_ = lean_array_push(v___x_5147_, v___x_5145_);
v_elseIfs_5149_ = l_Array_append___redArg(v___x_5148_, v___y_5142_);
lean_dec_ref(v___y_5142_);
if (v___y_5143_ == 0)
{
lean_object* v___x_5150_; lean_object* v___x_5151_; 
v___x_5150_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5149_, v_elseTk_5138_, v_elseBlock_5139_, v___y_5143_);
v___x_5151_ = l_Lean_Fmt_TaggedDoc_unflattenable(v___x_5150_);
return v___x_5151_;
}
else
{
lean_object* v___x_5152_; lean_object* v___x_5153_; uint8_t v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; 
lean_inc_ref(v_elseBlock_5139_);
lean_inc_ref(v_elseTk_5138_);
lean_inc_ref(v_elseIfs_5149_);
v___x_5152_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5149_, v_elseTk_5138_, v_elseBlock_5139_, v___y_5143_);
v___x_5153_ = l_Lean_Fmt_TaggedDoc_flattened(v___x_5152_);
v___x_5154_ = 0;
v___x_5155_ = l___private_Lean_Fmt_FmtM_Layouts_0__Lean_Fmt_Layouts_conditional_mk(v_elseIfs_5149_, v_elseTk_5138_, v_elseBlock_5139_, v___x_5154_);
v___x_5156_ = lean_unsigned_to_nat(2u);
v___x_5157_ = lean_mk_empty_array_with_capacity(v___x_5156_);
v___x_5158_ = lean_array_push(v___x_5157_, v___x_5153_);
v___x_5159_ = lean_array_push(v___x_5158_, v___x_5155_);
v___x_5160_ = l_Lean_Fmt_TaggedDoc_oneOf(v___x_5159_);
return v___x_5160_;
}
}
v___jp_5161_:
{
if (v_allowFlattening_5140_ == 0)
{
v___y_5142_ = v___y_5162_;
v___y_5143_ = v_allowFlattening_5140_;
goto v___jp_5141_;
}
else
{
lean_object* v___x_5163_; lean_object* v___x_5164_; uint8_t v___x_5165_; 
v___x_5163_ = lean_array_get_size(v___y_5162_);
v___x_5164_ = lean_unsigned_to_nat(0u);
v___x_5165_ = lean_nat_dec_eq(v___x_5163_, v___x_5164_);
v___y_5142_ = v___y_5162_;
v___y_5143_ = v___x_5165_;
goto v___jp_5141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_conditional___boxed(lean_object* v_ifTk_5177_, lean_object* v_cond_5178_, lean_object* v_thenTk_5179_, lean_object* v_thenBlock_5180_, lean_object* v_elseIfs_5181_, lean_object* v_elseTk_5182_, lean_object* v_elseBlock_5183_, lean_object* v_allowFlattening_5184_){
_start:
{
uint8_t v_allowFlattening_boxed_5185_; lean_object* v_res_5186_; 
v_allowFlattening_boxed_5185_ = lean_unbox(v_allowFlattening_5184_);
v_res_5186_ = l_Lean_Fmt_Layouts_conditional(v_ifTk_5177_, v_cond_5178_, v_thenTk_5179_, v_thenBlock_5180_, v_elseIfs_5181_, v_elseTk_5182_, v_elseBlock_5183_, v_allowFlattening_boxed_5185_);
lean_dec_ref(v_elseIfs_5181_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Layouts_strLit(lean_object* v_prefix_5187_, lean_object* v_str_5188_){
_start:
{
lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; uint8_t v___x_5194_; lean_object* v___x_5195_; 
v___x_5189_ = lean_unsigned_to_nat(2u);
v___x_5190_ = lean_mk_empty_array_with_capacity(v___x_5189_);
v___x_5191_ = lean_array_push(v___x_5190_, v_prefix_5187_);
v___x_5192_ = lean_array_push(v___x_5191_, v_str_5188_);
v___x_5193_ = l_Lean_Fmt_Layouts_atomic(v___x_5192_);
lean_dec_ref(v___x_5192_);
v___x_5194_ = 0;
v___x_5195_ = l_Lean_Fmt_TaggedDoc_mkSelfDelimited(v___x_5193_, v___x_5194_);
return v___x_5195_;
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

// Lean compiler output
// Module: Lean.Fmt.Core.Basic
// Imports: public import Init.Data.Hashable public import Init.Data.Ord.Basic public import Std.Data.HashMap.Basic import Init.Data
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
uint16_t lean_uint16_lor(uint16_t, uint16_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint16_t lean_uint16_of_nat(lean_object*);
uint16_t lean_uint16_shift_left(uint16_t, uint16_t);
uint16_t lean_uint16_complement(uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t lean_bool_to_uint8(uint8_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint16_t lean_uint8_to_uint16(uint8_t);
uint16_t lean_uint16_shift_right(uint16_t, uint16_t);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_UInt8_toUInt64___boxed(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_UInt8_decEq___boxed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
lean_object* lean_array_to_list(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedFullnessState___aux__1;
LEAN_EXPORT uint8_t l_Lean_Fmt_instInhabitedFullnessState;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqFullnessState___aux__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqFullnessState___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqFullnessState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqFullnessState___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqFullnessState___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqFullnessState = (const lean_object*)&l_Lean_Fmt_instBEqFullnessState___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableFullnessState___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableFullnessState___aux__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instHashableFullnessState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHashableFullnessState___closed__0 = (const lean_object*)&l_Lean_Fmt_instHashableFullnessState___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instHashableFullnessState = (const lean_object*)&l_Lean_Fmt_instHashableFullnessState___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_mk(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullBefore(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullBefore___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullAfter(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullAfter___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialBefore(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialBefore___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialAfter(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialAfter___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullBefore(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullBefore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullAfter(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullAfter___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialBefore(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialBefore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialAfter(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialAfter___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_contains(uint16_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow(lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPred___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAny(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAny___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAll(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAll___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAny(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAny___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAll(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAll___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(uint8_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_newlineFailureSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Fmt_newlineFailureSet___closed__0;
LEAN_EXPORT uint16_t l_Lean_Fmt_newlineFailureSet;
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails___lam__0(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0;
LEAN_EXPORT uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet;
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0;
LEAN_EXPORT uint16_t l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet;
LEAN_EXPORT uint16_t l_Lean_Fmt_textFailureSet(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_textFailureSet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTagId___aux__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedTagId;
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqTagId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqTagId___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instBEqTagId = (const lean_object*)&l_Lean_Fmt_instBEqTagId___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableTagId___aux__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableTagId___aux__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instHashableTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHashableTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instHashableTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instHashableTagId = (const lean_object*)&l_Lean_Fmt_instHashableTagId___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instOrdTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instOrdTagId___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instOrdTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instOrdTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instOrdTagId = (const lean_object*)&l_Lean_Fmt_instOrdTagId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprTagId___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprTagId = (const lean_object*)&l_Lean_Fmt_instReprTagId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringTagId___aux__1(lean_object*);
static const lean_closure_object l_Lean_Fmt_instToStringTagId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instToStringTagId___closed__0 = (const lean_object*)&l_Lean_Fmt_instToStringTagId___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instToStringTagId = (const lean_object*)&l_Lean_Fmt_instToStringTagId___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instHAddTagIdNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHAddTagIdNat___closed__0 = (const lean_object*)&l_Lean_Fmt_instHAddTagIdNat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instHAddTagIdNat = (const lean_object*)&l_Lean_Fmt_instHAddTagIdNat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysEmptiness_max(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_Atomicness_max(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_instReprAssertion___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "<assertion>"};
static const lean_object* l_Lean_Fmt_instReprAssertion___lam__0___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instReprAssertion___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprAssertion___lam__0___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instReprAssertion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instReprAssertion___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instReprAssertion___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprAssertion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_instReprAssertion = (const lean_object*)&l_Lean_Fmt_instReprAssertion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override(lean_object*);
static const lean_ctor_object l_Lean_Fmt_Doc_newline___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_newline___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_newline___override___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_newline___override___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_Fmt_Doc_newline___override___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Doc_text___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_text___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_text___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_either___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_either___override___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_either___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_either___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(uint8_t, uint16_t, uint8_t, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(uint16_t, uint8_t, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(uint16_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(uint8_t, uint16_t, uint16_t, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(uint16_t, lean_object*, uint16_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(uint16_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15(uint16_t, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(uint16_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21(uint16_t, lean_object*, lean_object*, uint16_t, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(uint16_t, uint8_t, lean_object*, lean_object*, lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc(lean_object*);
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.failure"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__2;
static lean_once_cell_t l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__3;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.newline"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__6_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Fmt.Doc.text"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__7 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__7_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.tagged"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__12_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Fmt.Doc.flattened"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__15_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Fmt.Doc.unflattenable"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__17_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__18_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Fmt.Doc.indented"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__19_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__20 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__20_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__20_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__21 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__21_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.aligned"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__22 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__22_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__23 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__23_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__23_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__24 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__24_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Fmt.Doc.unindented"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__25 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__25_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__25_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__26 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__26_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__27 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__27_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lean.Fmt.Doc.final"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__30 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__30_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.initial"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__32 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__33_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Fmt.Doc.free"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__35 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__36_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.guarded"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__37 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value),((lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__40 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__41 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__41_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.costing"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__42 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__43 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__44 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__44_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.either"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__45 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__46 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__47 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__47_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.append"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__48 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__48_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__48_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__49 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__49_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__49_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__50 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__50_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Doc_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_Doc_empty___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_empty___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_empty___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Doc_nl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Fmt_Doc_nl___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_nl___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_nl___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_nl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_nl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_nl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_break___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_break___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_break___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_break___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_hardNl___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_hardNl___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_hardNl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_hardNl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instAppendDoc___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instAppendDoc___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instAppendDoc___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instAppendDoc___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0_value;
static const lean_array_object l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqPtrKey___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqPtrKey___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqPtrKey___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instHashablePtrKey___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instHashablePtrKey___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_instHashablePtrKey___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg();
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_beq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___redArg___closed__0;
static lean_once_cell_t l_Lean_Fmt_Doc_beq___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_beq___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable(lean_object*, lean_object*, lean_object*);
static uint8_t _init_l_Lean_Fmt_instInhabitedFullnessState___aux__1(void){
_start:
{
uint8_t v___x_1_; 
v___x_1_ = 0;
return v___x_1_;
}
}
static uint8_t _init_l_Lean_Fmt_instInhabitedFullnessState(void){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = 0;
return v___x_2_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqFullnessState___aux__1(uint8_t v_a_3_, uint8_t v_b_4_){
_start:
{
uint8_t v___x_5_; 
v___x_5_ = lean_uint8_dec_eq(v_a_3_, v_b_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqFullnessState___aux__1___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_a_boxed_8_; uint8_t v_b_boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v_a_boxed_8_ = lean_unbox(v_a_6_);
v_b_boxed_9_ = lean_unbox(v_b_7_);
v_res_10_ = l_Lean_Fmt_instBEqFullnessState___aux__1(v_a_boxed_8_, v_b_boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableFullnessState___aux__1(uint8_t v_n_14_){
_start:
{
uint64_t v___x_15_; 
v___x_15_ = lean_uint8_to_uint64(v_n_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableFullnessState___aux__1___boxed(lean_object* v_n_16_){
_start:
{
uint8_t v_n_boxed_17_; uint64_t v_res_18_; lean_object* v_r_19_; 
v_n_boxed_17_ = lean_unbox(v_n_16_);
v_res_18_ = l_Lean_Fmt_instHashableFullnessState___aux__1(v_n_boxed_17_);
v_r_19_ = lean_box_uint64(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_mk(uint8_t v_isFullBefore_22_, uint8_t v_isFullAfter_23_, uint8_t v_isInitialBefore_24_, uint8_t v_isInitialAfter_25_){
_start:
{
uint8_t v___x_26_; uint8_t v___x_27_; uint8_t v___x_28_; uint8_t v___x_29_; uint8_t v___x_30_; uint8_t v___x_31_; uint8_t v___x_32_; uint8_t v___x_33_; uint8_t v___x_34_; uint8_t v___x_35_; uint8_t v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; 
v___x_26_ = lean_bool_to_uint8(v_isInitialBefore_24_);
v___x_27_ = 3;
v___x_28_ = lean_uint8_shift_left(v___x_26_, v___x_27_);
v___x_29_ = lean_bool_to_uint8(v_isInitialAfter_25_);
v___x_30_ = 2;
v___x_31_ = lean_uint8_shift_left(v___x_29_, v___x_30_);
v___x_32_ = lean_uint8_lor(v___x_28_, v___x_31_);
v___x_33_ = lean_bool_to_uint8(v_isFullBefore_22_);
v___x_34_ = 1;
v___x_35_ = lean_uint8_shift_left(v___x_33_, v___x_34_);
v___x_36_ = lean_uint8_lor(v___x_32_, v___x_35_);
v___x_37_ = lean_bool_to_uint8(v_isFullAfter_23_);
v___x_38_ = lean_uint8_lor(v___x_36_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_mk___boxed(lean_object* v_isFullBefore_39_, lean_object* v_isFullAfter_40_, lean_object* v_isInitialBefore_41_, lean_object* v_isInitialAfter_42_){
_start:
{
uint8_t v_isFullBefore_boxed_43_; uint8_t v_isFullAfter_boxed_44_; uint8_t v_isInitialBefore_boxed_45_; uint8_t v_isInitialAfter_boxed_46_; uint8_t v_res_47_; lean_object* v_r_48_; 
v_isFullBefore_boxed_43_ = lean_unbox(v_isFullBefore_39_);
v_isFullAfter_boxed_44_ = lean_unbox(v_isFullAfter_40_);
v_isInitialBefore_boxed_45_ = lean_unbox(v_isInitialBefore_41_);
v_isInitialAfter_boxed_46_ = lean_unbox(v_isInitialAfter_42_);
v_res_47_ = l_Lean_Fmt_FullnessState_mk(v_isFullBefore_boxed_43_, v_isFullAfter_boxed_44_, v_isInitialBefore_boxed_45_, v_isInitialAfter_boxed_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullBefore(uint8_t v_s_49_){
_start:
{
uint8_t v___x_50_; uint8_t v___x_51_; uint8_t v___x_52_; uint8_t v___x_53_; 
v___x_50_ = 2;
v___x_51_ = lean_uint8_land(v_s_49_, v___x_50_);
v___x_52_ = 0;
v___x_53_ = lean_uint8_dec_eq(v___x_51_, v___x_52_);
if (v___x_53_ == 0)
{
uint8_t v___x_54_; 
v___x_54_ = 1;
return v___x_54_;
}
else
{
uint8_t v___x_55_; 
v___x_55_ = 0;
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullBefore___boxed(lean_object* v_s_56_){
_start:
{
uint8_t v_s_boxed_57_; uint8_t v_res_58_; lean_object* v_r_59_; 
v_s_boxed_57_ = lean_unbox(v_s_56_);
v_res_58_ = l_Lean_Fmt_FullnessState_isFullBefore(v_s_boxed_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullAfter(uint8_t v_s_60_){
_start:
{
uint8_t v___x_61_; uint8_t v___x_62_; uint8_t v___x_63_; uint8_t v___x_64_; 
v___x_61_ = 1;
v___x_62_ = lean_uint8_land(v_s_60_, v___x_61_);
v___x_63_ = 0;
v___x_64_ = lean_uint8_dec_eq(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 1;
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullAfter___boxed(lean_object* v_s_67_){
_start:
{
uint8_t v_s_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v_s_boxed_68_ = lean_unbox(v_s_67_);
v_res_69_ = l_Lean_Fmt_FullnessState_isFullAfter(v_s_boxed_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialBefore(uint8_t v_s_71_){
_start:
{
uint8_t v___x_72_; uint8_t v___x_73_; uint8_t v___x_74_; uint8_t v___x_75_; 
v___x_72_ = 8;
v___x_73_ = lean_uint8_land(v_s_71_, v___x_72_);
v___x_74_ = 0;
v___x_75_ = lean_uint8_dec_eq(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
else
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialBefore___boxed(lean_object* v_s_78_){
_start:
{
uint8_t v_s_boxed_79_; uint8_t v_res_80_; lean_object* v_r_81_; 
v_s_boxed_79_ = lean_unbox(v_s_78_);
v_res_80_ = l_Lean_Fmt_FullnessState_isInitialBefore(v_s_boxed_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isInitialAfter(uint8_t v_s_82_){
_start:
{
uint8_t v___x_83_; uint8_t v___x_84_; uint8_t v___x_85_; uint8_t v___x_86_; 
v___x_83_ = 4;
v___x_84_ = lean_uint8_land(v_s_82_, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_uint8_dec_eq(v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isInitialAfter___boxed(lean_object* v_s_89_){
_start:
{
uint8_t v_s_boxed_90_; uint8_t v_res_91_; lean_object* v_r_92_; 
v_s_boxed_90_ = lean_unbox(v_s_89_);
v_res_91_ = l_Lean_Fmt_FullnessState_isInitialAfter(v_s_boxed_90_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullBefore(uint8_t v_s_93_, uint8_t v_isFullBefore_94_){
_start:
{
uint8_t v___x_95_; uint8_t v___x_96_; uint8_t v___x_97_; uint8_t v___x_98_; uint8_t v___x_99_; uint8_t v___x_100_; 
v___x_95_ = 253;
v___x_96_ = lean_uint8_land(v_s_93_, v___x_95_);
v___x_97_ = lean_bool_to_uint8(v_isFullBefore_94_);
v___x_98_ = 1;
v___x_99_ = lean_uint8_shift_left(v___x_97_, v___x_98_);
v___x_100_ = lean_uint8_lor(v___x_96_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullBefore___boxed(lean_object* v_s_101_, lean_object* v_isFullBefore_102_){
_start:
{
uint8_t v_s_boxed_103_; uint8_t v_isFullBefore_boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_s_boxed_103_ = lean_unbox(v_s_101_);
v_isFullBefore_boxed_104_ = lean_unbox(v_isFullBefore_102_);
v_res_105_ = l_Lean_Fmt_FullnessState_setFullBefore(v_s_boxed_103_, v_isFullBefore_boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullAfter(uint8_t v_s_107_, uint8_t v_isFullAfter_108_){
_start:
{
uint8_t v___x_109_; uint8_t v___x_110_; uint8_t v___x_111_; uint8_t v___x_112_; 
v___x_109_ = 254;
v___x_110_ = lean_uint8_land(v_s_107_, v___x_109_);
v___x_111_ = lean_bool_to_uint8(v_isFullAfter_108_);
v___x_112_ = lean_uint8_lor(v___x_110_, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullAfter___boxed(lean_object* v_s_113_, lean_object* v_isFullAfter_114_){
_start:
{
uint8_t v_s_boxed_115_; uint8_t v_isFullAfter_boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v_s_boxed_115_ = lean_unbox(v_s_113_);
v_isFullAfter_boxed_116_ = lean_unbox(v_isFullAfter_114_);
v_res_117_ = l_Lean_Fmt_FullnessState_setFullAfter(v_s_boxed_115_, v_isFullAfter_boxed_116_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialBefore(uint8_t v_s_119_, uint8_t v_isInitialBefore_120_){
_start:
{
uint8_t v___x_121_; uint8_t v___x_122_; uint8_t v___x_123_; uint8_t v___x_124_; uint8_t v___x_125_; uint8_t v___x_126_; 
v___x_121_ = 247;
v___x_122_ = lean_uint8_land(v_s_119_, v___x_121_);
v___x_123_ = lean_bool_to_uint8(v_isInitialBefore_120_);
v___x_124_ = 3;
v___x_125_ = lean_uint8_shift_left(v___x_123_, v___x_124_);
v___x_126_ = lean_uint8_lor(v___x_122_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialBefore___boxed(lean_object* v_s_127_, lean_object* v_isInitialBefore_128_){
_start:
{
uint8_t v_s_boxed_129_; uint8_t v_isInitialBefore_boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_s_boxed_129_ = lean_unbox(v_s_127_);
v_isInitialBefore_boxed_130_ = lean_unbox(v_isInitialBefore_128_);
v_res_131_ = l_Lean_Fmt_FullnessState_setInitialBefore(v_s_boxed_129_, v_isInitialBefore_boxed_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setInitialAfter(uint8_t v_s_133_, uint8_t v_isInitialAfter_134_){
_start:
{
uint8_t v___x_135_; uint8_t v___x_136_; uint8_t v___x_137_; uint8_t v___x_138_; uint8_t v___x_139_; uint8_t v___x_140_; 
v___x_135_ = 251;
v___x_136_ = lean_uint8_land(v_s_133_, v___x_135_);
v___x_137_ = lean_bool_to_uint8(v_isInitialAfter_134_);
v___x_138_ = 2;
v___x_139_ = lean_uint8_shift_left(v___x_137_, v___x_138_);
v___x_140_ = lean_uint8_lor(v___x_136_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setInitialAfter___boxed(lean_object* v_s_141_, lean_object* v_isInitialAfter_142_){
_start:
{
uint8_t v_s_boxed_143_; uint8_t v_isInitialAfter_boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_s_boxed_143_ = lean_unbox(v_s_141_);
v_isInitialAfter_boxed_144_ = lean_unbox(v_isInitialAfter_142_);
v_res_145_ = l_Lean_Fmt_FullnessState_setInitialAfter(v_s_boxed_143_, v_isInitialAfter_boxed_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_contains(uint16_t v_set_147_, uint8_t v_s_148_){
_start:
{
uint16_t v___x_149_; uint16_t v___x_150_; uint16_t v___x_151_; uint16_t v___x_152_; uint16_t v___x_153_; uint8_t v___x_154_; 
v___x_149_ = lean_uint8_to_uint16(v_s_148_);
v___x_150_ = lean_uint16_shift_right(v_set_147_, v___x_149_);
v___x_151_ = 1;
v___x_152_ = lean_uint16_land(v___x_150_, v___x_151_);
v___x_153_ = 0;
v___x_154_ = lean_uint16_dec_eq(v___x_152_, v___x_153_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; 
v___x_155_ = 1;
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 0;
return v___x_156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_contains___boxed(lean_object* v_set_157_, lean_object* v_s_158_){
_start:
{
uint16_t v_set_boxed_159_; uint8_t v_s_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_set_boxed_159_ = lean_unbox(v_set_157_);
v_s_boxed_160_ = lean_unbox(v_s_158_);
v_res_161_ = l_Lean_Fmt_FullnessStateSet_contains(v_set_boxed_159_, v_s_boxed_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow(lean_object* v_p_163_, lean_object* v_x_164_, uint16_t v_x_165_){
_start:
{
lean_object* v_zero_166_; uint8_t v_isZero_167_; 
v_zero_166_ = lean_unsigned_to_nat(0u);
v_isZero_167_ = lean_nat_dec_eq(v_x_164_, v_zero_166_);
if (v_isZero_167_ == 1)
{
lean_dec(v_x_164_);
lean_dec_ref(v_p_163_);
return v_x_165_;
}
else
{
lean_object* v_one_168_; lean_object* v_n_169_; uint8_t v_s_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_one_168_ = lean_unsigned_to_nat(1u);
v_n_169_ = lean_nat_sub(v_x_164_, v_one_168_);
lean_dec(v_x_164_);
v_s_170_ = lean_uint8_of_nat(v_n_169_);
v___x_171_ = lean_box(v_s_170_);
lean_inc_ref(v_p_163_);
v___x_172_ = lean_apply_1(v_p_163_, v___x_171_);
v___x_173_ = lean_unbox(v___x_172_);
if (v___x_173_ == 0)
{
v_x_164_ = v_n_169_;
goto _start;
}
else
{
uint16_t v___x_175_; uint16_t v___x_176_; uint16_t v___x_177_; uint16_t v___x_178_; 
v___x_175_ = 1;
v___x_176_ = lean_uint16_of_nat(v_n_169_);
v___x_177_ = lean_uint16_shift_left(v___x_175_, v___x_176_);
v___x_178_ = lean_uint16_lor(v_x_165_, v___x_177_);
v_x_164_ = v_n_169_;
v_x_165_ = v___x_178_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___boxed(lean_object* v_p_180_, lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
uint16_t v_x_68__boxed_183_; uint16_t v_res_184_; lean_object* v_r_185_; 
v_x_68__boxed_183_ = lean_unbox(v_x_182_);
v_res_184_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow(v_p_180_, v_x_181_, v_x_68__boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPred(lean_object* v_p_186_){
_start:
{
lean_object* v___x_187_; uint16_t v___x_188_; uint16_t v___x_189_; 
v___x_187_ = lean_unsigned_to_nat(16u);
v___x_188_ = 0;
v___x_189_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow(v_p_186_, v___x_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPred___boxed(lean_object* v_p_190_){
_start:
{
uint16_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Fmt_FullnessStateSet_ofPred(v_p_190_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAny(uint16_t v_inner_193_){
_start:
{
uint16_t v___x_194_; uint16_t v___x_195_; uint16_t v___x_196_; uint16_t v___x_197_; uint16_t v___x_198_; 
v___x_194_ = 1;
v___x_195_ = lean_uint16_shift_left(v_inner_193_, v___x_194_);
v___x_196_ = lean_uint16_lor(v___x_195_, v_inner_193_);
v___x_197_ = 43690;
v___x_198_ = lean_uint16_land(v___x_196_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAny___boxed(lean_object* v_inner_199_){
_start:
{
uint16_t v_inner_boxed_200_; uint16_t v_res_201_; lean_object* v_r_202_; 
v_inner_boxed_200_ = lean_unbox(v_inner_199_);
v_res_201_ = l_Lean_Fmt_FullnessStateSet_finalAny(v_inner_boxed_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_finalAll(uint16_t v_inner_203_){
_start:
{
uint16_t v___x_204_; uint16_t v___x_205_; uint16_t v___x_206_; uint16_t v___x_207_; uint16_t v___x_208_; 
v___x_204_ = 1;
v___x_205_ = lean_uint16_shift_left(v_inner_203_, v___x_204_);
v___x_206_ = lean_uint16_land(v___x_205_, v_inner_203_);
v___x_207_ = 43690;
v___x_208_ = lean_uint16_land(v___x_206_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_finalAll___boxed(lean_object* v_inner_209_){
_start:
{
uint16_t v_inner_boxed_210_; uint16_t v_res_211_; lean_object* v_r_212_; 
v_inner_boxed_210_ = lean_unbox(v_inner_209_);
v_res_211_ = l_Lean_Fmt_FullnessStateSet_finalAll(v_inner_boxed_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAny(uint16_t v_inner_213_){
_start:
{
uint16_t v___x_214_; uint16_t v___x_215_; uint16_t v___x_216_; uint16_t v___x_217_; uint16_t v___x_218_; 
v___x_214_ = 8;
v___x_215_ = lean_uint16_shift_left(v_inner_213_, v___x_214_);
v___x_216_ = lean_uint16_lor(v___x_215_, v_inner_213_);
v___x_217_ = 65280;
v___x_218_ = lean_uint16_land(v___x_216_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAny___boxed(lean_object* v_inner_219_){
_start:
{
uint16_t v_inner_boxed_220_; uint16_t v_res_221_; lean_object* v_r_222_; 
v_inner_boxed_220_ = lean_unbox(v_inner_219_);
v_res_221_ = l_Lean_Fmt_FullnessStateSet_initialAny(v_inner_boxed_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_initialAll(uint16_t v_inner_223_){
_start:
{
uint16_t v___x_224_; uint16_t v___x_225_; uint16_t v___x_226_; uint16_t v___x_227_; uint16_t v___x_228_; 
v___x_224_ = 8;
v___x_225_ = lean_uint16_shift_left(v_inner_223_, v___x_224_);
v___x_226_ = lean_uint16_land(v___x_225_, v_inner_223_);
v___x_227_ = 65280;
v___x_228_ = lean_uint16_land(v___x_226_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_initialAll___boxed(lean_object* v_inner_229_){
_start:
{
uint16_t v_inner_boxed_230_; uint16_t v_res_231_; lean_object* v_r_232_; 
v_inner_boxed_230_ = lean_unbox(v_inner_229_);
v_res_231_ = l_Lean_Fmt_FullnessStateSet_initialAll(v_inner_boxed_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(uint8_t v_s_233_, lean_object* v_p_234_, uint8_t v_isMidFull_235_, uint8_t v_isMidInitial_236_){
_start:
{
uint8_t v___x_237_; uint8_t v___x_238_; uint8_t v___x_239_; uint8_t v___x_240_; uint8_t v___x_241_; uint8_t v___x_242_; uint8_t v___x_243_; uint8_t v___x_244_; uint8_t v___x_245_; uint8_t v___x_246_; uint8_t v___x_247_; uint8_t v___x_248_; uint8_t v___x_249_; uint8_t v___x_250_; uint8_t v___x_251_; uint8_t v___x_252_; uint8_t v___x_253_; uint8_t v___x_254_; uint8_t v___x_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_237_ = 254;
v___x_238_ = lean_uint8_land(v_s_233_, v___x_237_);
v___x_239_ = lean_bool_to_uint8(v_isMidFull_235_);
v___x_240_ = lean_uint8_lor(v___x_238_, v___x_239_);
v___x_241_ = 251;
v___x_242_ = lean_uint8_land(v___x_240_, v___x_241_);
v___x_243_ = lean_bool_to_uint8(v_isMidInitial_236_);
v___x_244_ = 2;
v___x_245_ = lean_uint8_shift_left(v___x_243_, v___x_244_);
v___x_246_ = lean_uint8_lor(v___x_242_, v___x_245_);
v___x_247_ = 253;
v___x_248_ = lean_uint8_land(v_s_233_, v___x_247_);
v___x_249_ = 1;
v___x_250_ = lean_uint8_shift_left(v___x_239_, v___x_249_);
v___x_251_ = lean_uint8_lor(v___x_248_, v___x_250_);
v___x_252_ = 247;
v___x_253_ = lean_uint8_land(v___x_251_, v___x_252_);
v___x_254_ = 3;
v___x_255_ = lean_uint8_shift_left(v___x_243_, v___x_254_);
v___x_256_ = lean_uint8_lor(v___x_253_, v___x_255_);
v___x_257_ = lean_box(v___x_246_);
v___x_258_ = lean_box(v___x_256_);
v___x_259_ = lean_apply_2(v_p_234_, v___x_257_, v___x_258_);
v___x_260_ = lean_unbox(v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__0___boxed(lean_object* v_s_261_, lean_object* v_p_262_, lean_object* v_isMidFull_263_, lean_object* v_isMidInitial_264_){
_start:
{
uint8_t v_s_boxed_265_; uint8_t v_isMidFull_boxed_266_; uint8_t v_isMidInitial_boxed_267_; uint8_t v_res_268_; lean_object* v_r_269_; 
v_s_boxed_265_ = lean_unbox(v_s_261_);
v_isMidFull_boxed_266_ = lean_unbox(v_isMidFull_263_);
v_isMidInitial_boxed_267_ = lean_unbox(v_isMidInitial_264_);
v_res_268_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_boxed_265_, v_p_262_, v_isMidFull_boxed_266_, v_isMidInitial_boxed_267_);
v_r_269_ = lean_box(v_res_268_);
return v_r_269_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_anySplit___lam__1(lean_object* v_p_270_, uint8_t v_s_271_){
_start:
{
uint8_t v___x_272_; uint8_t v___x_273_; 
v___x_272_ = 0;
lean_inc_ref(v_p_270_);
v___x_273_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_272_, v___x_272_);
if (v___x_273_ == 0)
{
uint8_t v___x_274_; uint8_t v___x_275_; 
v___x_274_ = 1;
lean_inc_ref(v_p_270_);
v___x_275_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
uint8_t v___x_276_; 
lean_inc_ref(v_p_270_);
v___x_276_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
uint8_t v___x_277_; 
v___x_277_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__0(v_s_271_, v_p_270_, v___x_274_, v___x_274_);
return v___x_277_;
}
else
{
lean_dec_ref(v_p_270_);
return v___x_276_;
}
}
else
{
lean_dec_ref(v_p_270_);
return v___x_275_;
}
}
else
{
lean_dec_ref(v_p_270_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___lam__1___boxed(lean_object* v_p_278_, lean_object* v_s_279_){
_start:
{
uint8_t v_s_boxed_280_; uint8_t v_res_281_; lean_object* v_r_282_; 
v_s_boxed_280_ = lean_unbox(v_s_279_);
v_res_281_ = l_Lean_Fmt_FullnessStateSet_anySplit___lam__1(v_p_278_, v_s_boxed_280_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit(lean_object* v_p_283_){
_start:
{
lean_object* v___f_284_; lean_object* v___x_285_; uint16_t v___x_286_; uint16_t v___x_287_; 
v___f_284_ = lean_alloc_closure((void*)(l_Lean_Fmt_FullnessStateSet_anySplit___lam__1___boxed), 2, 1);
lean_closure_set(v___f_284_, 0, v_p_283_);
v___x_285_ = lean_unsigned_to_nat(16u);
v___x_286_ = 0;
v___x_287_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow(v___f_284_, v___x_285_, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___boxed(lean_object* v_p_288_){
_start:
{
uint16_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lean_Fmt_FullnessStateSet_anySplit(v_p_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(lean_object* v_x_291_, uint16_t v_x_292_){
_start:
{
lean_object* v_zero_293_; uint8_t v_isZero_294_; 
v_zero_293_ = lean_unsigned_to_nat(0u);
v_isZero_294_ = lean_nat_dec_eq(v_x_291_, v_zero_293_);
if (v_isZero_294_ == 1)
{
lean_dec(v_x_291_);
return v_x_292_;
}
else
{
lean_object* v_one_295_; lean_object* v_n_296_; uint8_t v_s_303_; uint8_t v___x_304_; uint8_t v___x_305_; uint8_t v___x_306_; uint8_t v___x_307_; 
v_one_295_ = lean_unsigned_to_nat(1u);
v_n_296_ = lean_nat_sub(v_x_291_, v_one_295_);
lean_dec(v_x_291_);
v_s_303_ = lean_uint8_of_nat(v_n_296_);
v___x_304_ = 1;
v___x_305_ = lean_uint8_land(v_s_303_, v___x_304_);
v___x_306_ = 0;
v___x_307_ = lean_uint8_dec_eq(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
goto v___jp_297_;
}
else
{
uint8_t v___x_308_; uint8_t v___x_309_; uint8_t v___x_310_; 
v___x_308_ = 8;
v___x_309_ = lean_uint8_land(v_s_303_, v___x_308_);
v___x_310_ = lean_uint8_dec_eq(v___x_309_, v___x_306_);
if (v___x_310_ == 0)
{
goto v___jp_297_;
}
else
{
v_x_291_ = v_n_296_;
goto _start;
}
}
v___jp_297_:
{
uint16_t v___x_298_; uint16_t v___x_299_; uint16_t v___x_300_; uint16_t v___x_301_; 
v___x_298_ = 1;
v___x_299_ = lean_uint16_of_nat(v_n_296_);
v___x_300_ = lean_uint16_shift_left(v___x_298_, v___x_299_);
v___x_301_ = lean_uint16_lor(v_x_292_, v___x_300_);
v_x_291_ = v_n_296_;
v_x_292_ = v___x_301_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0___boxed(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint16_t v_x_141__boxed_314_; uint16_t v_res_315_; lean_object* v_r_316_; 
v_x_141__boxed_314_ = lean_unbox(v_x_313_);
v_res_315_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(v_x_312_, v_x_141__boxed_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
static uint16_t _init_l_Lean_Fmt_newlineFailureSet___closed__0(void){
_start:
{
uint16_t v___x_317_; lean_object* v___x_318_; uint16_t v___x_319_; 
v___x_317_ = 0;
v___x_318_ = lean_unsigned_to_nat(16u);
v___x_319_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_newlineFailureSet_spec__0(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static uint16_t _init_l_Lean_Fmt_newlineFailureSet(void){
_start:
{
uint16_t v___x_320_; 
v___x_320_ = lean_uint16_once(&l_Lean_Fmt_newlineFailureSet___closed__0, &l_Lean_Fmt_newlineFailureSet___closed__0_once, _init_l_Lean_Fmt_newlineFailureSet___closed__0);
return v___x_320_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails___lam__0(uint8_t v_isEmpty_321_, uint8_t v_before_322_, uint8_t v_after_323_){
_start:
{
if (v_before_322_ == 0)
{
return v_after_323_;
}
else
{
if (v_after_323_ == 0)
{
return v_before_322_;
}
else
{
if (v_isEmpty_321_ == 0)
{
return v_after_323_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = 0;
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___lam__0___boxed(lean_object* v_isEmpty_325_, lean_object* v_before_326_, lean_object* v_after_327_){
_start:
{
uint8_t v_isEmpty_boxed_328_; uint8_t v_before_boxed_329_; uint8_t v_after_boxed_330_; uint8_t v_res_331_; lean_object* v_r_332_; 
v_isEmpty_boxed_328_ = lean_unbox(v_isEmpty_325_);
v_before_boxed_329_ = lean_unbox(v_before_326_);
v_after_boxed_330_ = lean_unbox(v_after_327_);
v_res_331_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_boxed_328_, v_before_boxed_329_, v_after_boxed_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_textFails(uint8_t v_isEmpty_333_, uint8_t v_state_334_){
_start:
{
uint8_t v___y_336_; uint8_t v___y_337_; uint8_t v___y_346_; uint8_t v___y_347_; uint8_t v___y_355_; uint8_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; uint8_t v___x_365_; 
v___x_362_ = 2;
v___x_363_ = lean_uint8_land(v_state_334_, v___x_362_);
v___x_364_ = 0;
v___x_365_ = lean_uint8_dec_eq(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
uint8_t v___x_366_; 
v___x_366_ = 1;
v___y_355_ = v___x_366_;
goto v___jp_354_;
}
else
{
uint8_t v___x_367_; 
v___x_367_ = 0;
v___y_355_ = v___x_367_;
goto v___jp_354_;
}
v___jp_335_:
{
uint8_t v___x_338_; uint8_t v___x_339_; uint8_t v___x_340_; uint8_t v___x_341_; 
v___x_338_ = 4;
v___x_339_ = lean_uint8_land(v_state_334_, v___x_338_);
v___x_340_ = 0;
v___x_341_ = lean_uint8_dec_eq(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; uint8_t v___x_343_; 
v___x_342_ = 1;
v___x_343_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_333_, v___y_337_, v___x_342_);
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_333_, v___y_337_, v___y_336_);
return v___x_344_;
}
}
v___jp_345_:
{
uint8_t v___x_348_; 
v___x_348_ = l_Lean_Fmt_textFails___lam__0(v_isEmpty_333_, v___y_346_, v___y_347_);
if (v___x_348_ == 0)
{
uint8_t v___x_349_; uint8_t v___x_350_; uint8_t v___x_351_; uint8_t v___x_352_; 
v___x_349_ = 8;
v___x_350_ = lean_uint8_land(v_state_334_, v___x_349_);
v___x_351_ = 0;
v___x_352_ = lean_uint8_dec_eq(v___x_350_, v___x_351_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 1;
v___y_336_ = v___x_348_;
v___y_337_ = v___x_353_;
goto v___jp_335_;
}
else
{
v___y_336_ = v___x_348_;
v___y_337_ = v___x_348_;
goto v___jp_335_;
}
}
else
{
return v___x_348_;
}
}
v___jp_354_:
{
uint8_t v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; uint8_t v___x_359_; 
v___x_356_ = 1;
v___x_357_ = lean_uint8_land(v_state_334_, v___x_356_);
v___x_358_ = 0;
v___x_359_ = lean_uint8_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
v___x_360_ = 1;
v___y_346_ = v___y_355_;
v___y_347_ = v___x_360_;
goto v___jp_345_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = 0;
v___y_346_ = v___y_355_;
v___y_347_ = v___x_361_;
goto v___jp_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_textFails___boxed(lean_object* v_isEmpty_368_, lean_object* v_state_369_){
_start:
{
uint8_t v_isEmpty_boxed_370_; uint8_t v_state_boxed_371_; uint8_t v_res_372_; lean_object* v_r_373_; 
v_isEmpty_boxed_370_ = lean_unbox(v_isEmpty_368_);
v_state_boxed_371_ = lean_unbox(v_state_369_);
v_res_372_ = l_Lean_Fmt_textFails(v_isEmpty_boxed_370_, v_state_boxed_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(lean_object* v_x_374_, uint16_t v_x_375_){
_start:
{
lean_object* v_zero_376_; uint8_t v_isZero_377_; 
v_zero_376_ = lean_unsigned_to_nat(0u);
v_isZero_377_ = lean_nat_dec_eq(v_x_374_, v_zero_376_);
if (v_isZero_377_ == 1)
{
lean_dec(v_x_374_);
return v_x_375_;
}
else
{
uint8_t v___x_378_; lean_object* v_one_379_; lean_object* v_n_380_; uint8_t v_s_381_; uint8_t v___x_382_; 
v___x_378_ = 1;
v_one_379_ = lean_unsigned_to_nat(1u);
v_n_380_ = lean_nat_sub(v_x_374_, v_one_379_);
lean_dec(v_x_374_);
v_s_381_ = lean_uint8_of_nat(v_n_380_);
v___x_382_ = l_Lean_Fmt_textFails(v___x_378_, v_s_381_);
if (v___x_382_ == 0)
{
v_x_374_ = v_n_380_;
goto _start;
}
else
{
uint16_t v___x_384_; uint16_t v___x_385_; uint16_t v___x_386_; uint16_t v___x_387_; 
v___x_384_ = 1;
v___x_385_ = lean_uint16_of_nat(v_n_380_);
v___x_386_ = lean_uint16_shift_left(v___x_384_, v___x_385_);
v___x_387_ = lean_uint16_lor(v_x_375_, v___x_386_);
v_x_374_ = v_n_380_;
v_x_375_ = v___x_387_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0___boxed(lean_object* v_x_389_, lean_object* v_x_390_){
_start:
{
uint16_t v_x_30__boxed_391_; uint16_t v_res_392_; lean_object* v_r_393_; 
v_x_30__boxed_391_ = lean_unbox(v_x_390_);
v_res_392_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(v_x_389_, v_x_30__boxed_391_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0(void){
_start:
{
uint16_t v___x_394_; lean_object* v___x_395_; uint16_t v___x_396_; 
v___x_394_ = 0;
v___x_395_ = lean_unsigned_to_nat(16u);
v___x_396_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet_spec__0(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet(void){
_start:
{
uint16_t v___x_397_; 
v___x_397_ = lean_uint16_once(&l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0, &l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0_once, _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet___closed__0);
return v___x_397_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(lean_object* v_x_398_, uint16_t v_x_399_){
_start:
{
lean_object* v_zero_400_; uint8_t v_isZero_401_; 
v_zero_400_ = lean_unsigned_to_nat(0u);
v_isZero_401_ = lean_nat_dec_eq(v_x_398_, v_zero_400_);
if (v_isZero_401_ == 1)
{
lean_dec(v_x_398_);
return v_x_399_;
}
else
{
lean_object* v_one_402_; lean_object* v_n_403_; uint8_t v_s_404_; uint8_t v___x_405_; 
v_one_402_ = lean_unsigned_to_nat(1u);
v_n_403_ = lean_nat_sub(v_x_398_, v_one_402_);
lean_dec(v_x_398_);
v_s_404_ = lean_uint8_of_nat(v_n_403_);
v___x_405_ = l_Lean_Fmt_textFails(v_isZero_401_, v_s_404_);
if (v___x_405_ == 0)
{
v_x_398_ = v_n_403_;
goto _start;
}
else
{
uint16_t v___x_407_; uint16_t v___x_408_; uint16_t v___x_409_; uint16_t v___x_410_; 
v___x_407_ = 1;
v___x_408_ = lean_uint16_of_nat(v_n_403_);
v___x_409_ = lean_uint16_shift_left(v___x_407_, v___x_408_);
v___x_410_ = lean_uint16_lor(v_x_399_, v___x_409_);
v_x_398_ = v_n_403_;
v_x_399_ = v___x_410_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0___boxed(lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
uint16_t v_x_30__boxed_414_; uint16_t v_res_415_; lean_object* v_r_416_; 
v_x_30__boxed_414_ = lean_unbox(v_x_413_);
v_res_415_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(v_x_412_, v_x_30__boxed_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0(void){
_start:
{
uint16_t v___x_417_; lean_object* v___x_418_; uint16_t v___x_419_; 
v___x_417_ = 0;
v___x_418_ = lean_unsigned_to_nat(16u);
v___x_419_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00__private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet_spec__0(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static uint16_t _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet(void){
_start:
{
uint16_t v___x_420_; 
v___x_420_ = lean_uint16_once(&l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0, &l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0_once, _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet___closed__0);
return v___x_420_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_textFailureSet(uint8_t v_isEmpty_421_){
_start:
{
if (v_isEmpty_421_ == 0)
{
uint16_t v___x_422_; 
v___x_422_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet;
return v___x_422_;
}
else
{
uint16_t v___x_423_; 
v___x_423_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet;
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_textFailureSet___boxed(lean_object* v_isEmpty_424_){
_start:
{
uint8_t v_isEmpty_boxed_425_; uint16_t v_res_426_; lean_object* v_r_427_; 
v_isEmpty_boxed_425_ = lean_unbox(v_isEmpty_424_);
v_res_426_ = l_Lean_Fmt_textFailureSet(v_isEmpty_boxed_425_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId___aux__1(void){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(0u);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_unsigned_to_nat(0u);
return v___x_429_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqTagId___aux__1(lean_object* v_a_430_, lean_object* v_b_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_eq(v_a_430_, v_b_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqTagId___aux__1___boxed(lean_object* v_a_433_, lean_object* v_b_434_){
_start:
{
uint8_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Lean_Fmt_instBEqTagId___aux__1(v_a_433_, v_b_434_);
lean_dec(v_b_434_);
lean_dec(v_a_433_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableTagId___aux__1(lean_object* v_n_439_){
_start:
{
uint64_t v___x_440_; 
v___x_440_ = lean_uint64_of_nat(v_n_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableTagId___aux__1___boxed(lean_object* v_n_441_){
_start:
{
uint64_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_Fmt_instHashableTagId___aux__1(v_n_441_);
lean_dec(v_n_441_);
v_r_443_ = lean_box_uint64(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___aux__1(lean_object* v_x_446_, lean_object* v_y_447_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_lt(v_x_446_, v_y_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = lean_nat_dec_eq(v_x_446_, v_y_447_);
if (v___x_449_ == 0)
{
uint8_t v___x_450_; 
v___x_450_ = 2;
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = 1;
return v___x_451_;
}
}
else
{
uint8_t v___x_452_; 
v___x_452_ = 0;
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___aux__1___boxed(lean_object* v_x_453_, lean_object* v_y_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Lean_Fmt_instOrdTagId___aux__1(v_x_453_, v_y_454_);
lean_dec(v_y_454_);
lean_dec(v_x_453_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___lam__0(lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_nat_dec_lt(v___y_457_, v___y_458_);
if (v___x_459_ == 0)
{
uint8_t v___x_460_; 
v___x_460_ = lean_nat_dec_eq(v___y_457_, v___y_458_);
if (v___x_460_ == 0)
{
uint8_t v___x_461_; 
v___x_461_ = 2;
return v___x_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = 1;
return v___x_462_;
}
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 0;
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___lam__0___boxed(lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_Fmt_instOrdTagId___lam__0(v___y_464_, v___y_465_);
lean_dec(v___y_465_);
lean_dec(v___y_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___redArg(lean_object* v_n_470_){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = l_Nat_reprFast(v_n_470_);
v___x_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1(lean_object* v_n_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = l_Nat_reprFast(v_n_473_);
v___x_476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___boxed(lean_object* v_n_477_, lean_object* v_x_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Fmt_instReprTagId___aux__1(v_n_477_, v_x_478_);
lean_dec(v_x_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0(lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = l_Nat_reprFast(v___y_480_);
v___x_483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0___boxed(lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Fmt_instReprTagId___lam__0(v___y_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringTagId___aux__1(lean_object* v_n_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Nat_reprFast(v_n_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1(lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_nat_add(v_a_493_, v_b_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1___boxed(lean_object* v_a_496_, lean_object* v_b_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Fmt_instHAddTagIdNat___aux__1(v_a_496_, v_b_497_);
lean_dec(v_b_497_);
lean_dec(v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx(uint8_t v_x_501_){
_start:
{
switch(v_x_501_)
{
case 0:
{
lean_object* v___x_502_; 
v___x_502_ = lean_unsigned_to_nat(0u);
return v___x_502_;
}
case 1:
{
lean_object* v___x_503_; 
v___x_503_ = lean_unsigned_to_nat(1u);
return v___x_503_;
}
default: 
{
lean_object* v___x_504_; 
v___x_504_ = lean_unsigned_to_nat(2u);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___boxed(lean_object* v_x_505_){
_start:
{
uint8_t v_x_boxed_506_; lean_object* v_res_507_; 
v_x_boxed_506_ = lean_unbox(v_x_505_);
v_res_507_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx(v_x_boxed_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(lean_object* v_k_508_){
_start:
{
lean_inc(v_k_508_);
return v_k_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg___boxed(lean_object* v_k_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(v_k_509_);
lean_dec(v_k_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(lean_object* v_motive_511_, lean_object* v_ctorIdx_512_, uint8_t v_t_513_, lean_object* v_h_514_, lean_object* v_k_515_){
_start:
{
lean_inc(v_k_515_);
return v_k_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___boxed(lean_object* v_motive_516_, lean_object* v_ctorIdx_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_k_520_){
_start:
{
uint8_t v_t_boxed_521_; lean_object* v_res_522_; 
v_t_boxed_521_ = lean_unbox(v_t_518_);
v_res_522_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(v_motive_516_, v_ctorIdx_517_, v_t_boxed_521_, v_h_519_, v_k_520_);
lean_dec(v_k_520_);
lean_dec(v_ctorIdx_517_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(lean_object* v_alwaysEmpty_523_){
_start:
{
lean_inc(v_alwaysEmpty_523_);
return v_alwaysEmpty_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg___boxed(lean_object* v_alwaysEmpty_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(v_alwaysEmpty_524_);
lean_dec(v_alwaysEmpty_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(lean_object* v_motive_526_, uint8_t v_t_527_, lean_object* v_h_528_, lean_object* v_alwaysEmpty_529_){
_start:
{
lean_inc(v_alwaysEmpty_529_);
return v_alwaysEmpty_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___boxed(lean_object* v_motive_530_, lean_object* v_t_531_, lean_object* v_h_532_, lean_object* v_alwaysEmpty_533_){
_start:
{
uint8_t v_t_boxed_534_; lean_object* v_res_535_; 
v_t_boxed_534_ = lean_unbox(v_t_531_);
v_res_535_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(v_motive_530_, v_t_boxed_534_, v_h_532_, v_alwaysEmpty_533_);
lean_dec(v_alwaysEmpty_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(lean_object* v_alwaysEmptyIfFlattened_536_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_536_);
return v_alwaysEmptyIfFlattened_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg___boxed(lean_object* v_alwaysEmptyIfFlattened_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(v_alwaysEmptyIfFlattened_537_);
lean_dec(v_alwaysEmptyIfFlattened_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(lean_object* v_motive_539_, uint8_t v_t_540_, lean_object* v_h_541_, lean_object* v_alwaysEmptyIfFlattened_542_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_542_);
return v_alwaysEmptyIfFlattened_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___boxed(lean_object* v_motive_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_alwaysEmptyIfFlattened_546_){
_start:
{
uint8_t v_t_boxed_547_; lean_object* v_res_548_; 
v_t_boxed_547_ = lean_unbox(v_t_544_);
v_res_548_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(v_motive_543_, v_t_boxed_547_, v_h_545_, v_alwaysEmptyIfFlattened_546_);
lean_dec(v_alwaysEmptyIfFlattened_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(lean_object* v_sometimesNonEmpty_549_){
_start:
{
lean_inc(v_sometimesNonEmpty_549_);
return v_sometimesNonEmpty_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg___boxed(lean_object* v_sometimesNonEmpty_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(v_sometimesNonEmpty_550_);
lean_dec(v_sometimesNonEmpty_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(lean_object* v_motive_552_, uint8_t v_t_553_, lean_object* v_h_554_, lean_object* v_sometimesNonEmpty_555_){
_start:
{
lean_inc(v_sometimesNonEmpty_555_);
return v_sometimesNonEmpty_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___boxed(lean_object* v_motive_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_sometimesNonEmpty_559_){
_start:
{
uint8_t v_t_boxed_560_; lean_object* v_res_561_; 
v_t_boxed_560_ = lean_unbox(v_t_557_);
v_res_561_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(v_motive_556_, v_t_boxed_560_, v_h_558_, v_sometimesNonEmpty_559_);
lean_dec(v_sometimesNonEmpty_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(uint8_t v_x_562_){
_start:
{
switch(v_x_562_)
{
case 0:
{
lean_object* v___x_563_; 
v___x_563_ = lean_unsigned_to_nat(0u);
return v___x_563_;
}
case 1:
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(1u);
return v___x_564_;
}
default: 
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(2u);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0___boxed(lean_object* v_x_566_){
_start:
{
uint8_t v_x_68__boxed_567_; lean_object* v_res_568_; 
v_x_68__boxed_567_ = lean_unbox(v_x_566_);
v_res_568_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_x_68__boxed_567_);
return v_res_568_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysEmptiness_max(uint8_t v_e1_569_, uint8_t v_e2_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e2_570_);
v___x_572_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e1_569_);
v___x_573_ = lean_nat_dec_le(v___x_571_, v___x_572_);
lean_dec(v___x_572_);
lean_dec(v___x_571_);
if (v___x_573_ == 0)
{
return v_e2_570_;
}
else
{
return v_e1_569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___boxed(lean_object* v_e1_574_, lean_object* v_e2_575_){
_start:
{
uint8_t v_e1_boxed_576_; uint8_t v_e2_boxed_577_; uint8_t v_res_578_; lean_object* v_r_579_; 
v_e1_boxed_576_ = lean_unbox(v_e1_574_);
v_e2_boxed_577_ = lean_unbox(v_e2_575_);
v_res_578_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v_e1_boxed_576_, v_e2_boxed_577_);
v_r_579_ = lean_box(v_res_578_);
return v_r_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx(uint8_t v_x_580_){
_start:
{
if (v_x_580_ == 0)
{
lean_object* v___x_581_; 
v___x_581_ = lean_unsigned_to_nat(0u);
return v___x_581_;
}
else
{
lean_object* v___x_582_; 
v___x_582_ = lean_unsigned_to_nat(1u);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___boxed(lean_object* v_x_583_){
_start:
{
uint8_t v_x_boxed_584_; lean_object* v_res_585_; 
v_x_boxed_584_ = lean_unbox(v_x_583_);
v_res_585_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx(v_x_boxed_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(lean_object* v_k_586_){
_start:
{
lean_inc(v_k_586_);
return v_k_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg___boxed(lean_object* v_k_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(v_k_587_);
lean_dec(v_k_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(lean_object* v_motive_589_, lean_object* v_ctorIdx_590_, uint8_t v_t_591_, lean_object* v_h_592_, lean_object* v_k_593_){
_start:
{
lean_inc(v_k_593_);
return v_k_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___boxed(lean_object* v_motive_594_, lean_object* v_ctorIdx_595_, lean_object* v_t_596_, lean_object* v_h_597_, lean_object* v_k_598_){
_start:
{
uint8_t v_t_boxed_599_; lean_object* v_res_600_; 
v_t_boxed_599_ = lean_unbox(v_t_596_);
v_res_600_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(v_motive_594_, v_ctorIdx_595_, v_t_boxed_599_, v_h_597_, v_k_598_);
lean_dec(v_k_598_);
lean_dec(v_ctorIdx_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(lean_object* v_alwaysNonEmpty_601_){
_start:
{
lean_inc(v_alwaysNonEmpty_601_);
return v_alwaysNonEmpty_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg___boxed(lean_object* v_alwaysNonEmpty_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(v_alwaysNonEmpty_602_);
lean_dec(v_alwaysNonEmpty_602_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(lean_object* v_motive_604_, uint8_t v_t_605_, lean_object* v_h_606_, lean_object* v_alwaysNonEmpty_607_){
_start:
{
lean_inc(v_alwaysNonEmpty_607_);
return v_alwaysNonEmpty_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___boxed(lean_object* v_motive_608_, lean_object* v_t_609_, lean_object* v_h_610_, lean_object* v_alwaysNonEmpty_611_){
_start:
{
uint8_t v_t_boxed_612_; lean_object* v_res_613_; 
v_t_boxed_612_ = lean_unbox(v_t_609_);
v_res_613_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(v_motive_608_, v_t_boxed_612_, v_h_610_, v_alwaysNonEmpty_611_);
lean_dec(v_alwaysNonEmpty_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(lean_object* v_sometimesEmpty_614_){
_start:
{
lean_inc(v_sometimesEmpty_614_);
return v_sometimesEmpty_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg___boxed(lean_object* v_sometimesEmpty_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(v_sometimesEmpty_615_);
lean_dec(v_sometimesEmpty_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(lean_object* v_motive_617_, uint8_t v_t_618_, lean_object* v_h_619_, lean_object* v_sometimesEmpty_620_){
_start:
{
lean_inc(v_sometimesEmpty_620_);
return v_sometimesEmpty_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___boxed(lean_object* v_motive_621_, lean_object* v_t_622_, lean_object* v_h_623_, lean_object* v_sometimesEmpty_624_){
_start:
{
uint8_t v_t_boxed_625_; lean_object* v_res_626_; 
v_t_boxed_625_ = lean_unbox(v_t_622_);
v_res_626_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(v_motive_621_, v_t_boxed_625_, v_h_623_, v_sometimesEmpty_624_);
lean_dec(v_sometimesEmpty_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(uint8_t v_x_627_){
_start:
{
if (v_x_627_ == 0)
{
lean_object* v___x_628_; 
v___x_628_ = lean_unsigned_to_nat(0u);
return v___x_628_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_unsigned_to_nat(1u);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0___boxed(lean_object* v_x_630_){
_start:
{
uint8_t v_x_50__boxed_631_; lean_object* v_res_632_; 
v_x_50__boxed_631_ = lean_unbox(v_x_630_);
v_res_632_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_x_50__boxed_631_);
return v_res_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(uint8_t v_e1_633_, uint8_t v_e2_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e2_634_);
v___x_636_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e1_633_);
v___x_637_ = lean_nat_dec_le(v___x_635_, v___x_636_);
lean_dec(v___x_636_);
lean_dec(v___x_635_);
if (v___x_637_ == 0)
{
return v_e2_634_;
}
else
{
return v_e1_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___boxed(lean_object* v_e1_638_, lean_object* v_e2_639_){
_start:
{
uint8_t v_e1_boxed_640_; uint8_t v_e2_boxed_641_; uint8_t v_res_642_; lean_object* v_r_643_; 
v_e1_boxed_640_ = lean_unbox(v_e1_638_);
v_e2_boxed_641_ = lean_unbox(v_e2_639_);
v_res_642_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v_e1_boxed_640_, v_e2_boxed_641_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx(uint8_t v_x_644_){
_start:
{
switch(v_x_644_)
{
case 0:
{
lean_object* v___x_645_; 
v___x_645_ = lean_unsigned_to_nat(0u);
return v___x_645_;
}
case 1:
{
lean_object* v___x_646_; 
v___x_646_ = lean_unsigned_to_nat(1u);
return v___x_646_;
}
case 2:
{
lean_object* v___x_647_; 
v___x_647_ = lean_unsigned_to_nat(2u);
return v___x_647_;
}
case 3:
{
lean_object* v___x_648_; 
v___x_648_ = lean_unsigned_to_nat(3u);
return v___x_648_;
}
default: 
{
lean_object* v___x_649_; 
v___x_649_ = lean_unsigned_to_nat(4u);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___boxed(lean_object* v_x_650_){
_start:
{
uint8_t v_x_boxed_651_; lean_object* v_res_652_; 
v_x_boxed_651_ = lean_unbox(v_x_650_);
v_res_652_ = l_Lean_Fmt_Doc_Atomicness_ctorIdx(v_x_boxed_651_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(lean_object* v_k_653_){
_start:
{
lean_inc(v_k_653_);
return v_k_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg___boxed(lean_object* v_k_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(v_k_654_);
lean_dec(v_k_654_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim(lean_object* v_motive_656_, lean_object* v_ctorIdx_657_, uint8_t v_t_658_, lean_object* v_h_659_, lean_object* v_k_660_){
_start:
{
lean_inc(v_k_660_);
return v_k_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___boxed(lean_object* v_motive_661_, lean_object* v_ctorIdx_662_, lean_object* v_t_663_, lean_object* v_h_664_, lean_object* v_k_665_){
_start:
{
uint8_t v_t_boxed_666_; lean_object* v_res_667_; 
v_t_boxed_666_ = lean_unbox(v_t_663_);
v_res_667_ = l_Lean_Fmt_Doc_Atomicness_ctorElim(v_motive_661_, v_ctorIdx_662_, v_t_boxed_666_, v_h_664_, v_k_665_);
lean_dec(v_k_665_);
lean_dec(v_ctorIdx_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(lean_object* v_atomic_668_){
_start:
{
lean_inc(v_atomic_668_);
return v_atomic_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg___boxed(lean_object* v_atomic_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(v_atomic_669_);
lean_dec(v_atomic_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim(lean_object* v_motive_671_, uint8_t v_t_672_, lean_object* v_h_673_, lean_object* v_atomic_674_){
_start:
{
lean_inc(v_atomic_674_);
return v_atomic_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___boxed(lean_object* v_motive_675_, lean_object* v_t_676_, lean_object* v_h_677_, lean_object* v_atomic_678_){
_start:
{
uint8_t v_t_boxed_679_; lean_object* v_res_680_; 
v_t_boxed_679_ = lean_unbox(v_t_676_);
v_res_680_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim(v_motive_675_, v_t_boxed_679_, v_h_677_, v_atomic_678_);
lean_dec(v_atomic_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(lean_object* v_atomicIfFlattened_681_){
_start:
{
lean_inc(v_atomicIfFlattened_681_);
return v_atomicIfFlattened_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg___boxed(lean_object* v_atomicIfFlattened_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(v_atomicIfFlattened_682_);
lean_dec(v_atomicIfFlattened_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(lean_object* v_motive_684_, uint8_t v_t_685_, lean_object* v_h_686_, lean_object* v_atomicIfFlattened_687_){
_start:
{
lean_inc(v_atomicIfFlattened_687_);
return v_atomicIfFlattened_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___boxed(lean_object* v_motive_688_, lean_object* v_t_689_, lean_object* v_h_690_, lean_object* v_atomicIfFlattened_691_){
_start:
{
uint8_t v_t_boxed_692_; lean_object* v_res_693_; 
v_t_boxed_692_ = lean_unbox(v_t_689_);
v_res_693_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(v_motive_688_, v_t_boxed_692_, v_h_690_, v_atomicIfFlattened_691_);
lean_dec(v_atomicIfFlattened_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(lean_object* v_compoundAtomic_694_){
_start:
{
lean_inc(v_compoundAtomic_694_);
return v_compoundAtomic_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg___boxed(lean_object* v_compoundAtomic_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(v_compoundAtomic_695_);
lean_dec(v_compoundAtomic_695_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(lean_object* v_motive_697_, uint8_t v_t_698_, lean_object* v_h_699_, lean_object* v_compoundAtomic_700_){
_start:
{
lean_inc(v_compoundAtomic_700_);
return v_compoundAtomic_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___boxed(lean_object* v_motive_701_, lean_object* v_t_702_, lean_object* v_h_703_, lean_object* v_compoundAtomic_704_){
_start:
{
uint8_t v_t_boxed_705_; lean_object* v_res_706_; 
v_t_boxed_705_ = lean_unbox(v_t_702_);
v_res_706_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(v_motive_701_, v_t_boxed_705_, v_h_703_, v_compoundAtomic_704_);
lean_dec(v_compoundAtomic_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(lean_object* v_compoundAtomicIfFlattened_707_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_707_);
return v_compoundAtomicIfFlattened_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg___boxed(lean_object* v_compoundAtomicIfFlattened_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(v_compoundAtomicIfFlattened_708_);
lean_dec(v_compoundAtomicIfFlattened_708_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(lean_object* v_motive_710_, uint8_t v_t_711_, lean_object* v_h_712_, lean_object* v_compoundAtomicIfFlattened_713_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_713_);
return v_compoundAtomicIfFlattened_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___boxed(lean_object* v_motive_714_, lean_object* v_t_715_, lean_object* v_h_716_, lean_object* v_compoundAtomicIfFlattened_717_){
_start:
{
uint8_t v_t_boxed_718_; lean_object* v_res_719_; 
v_t_boxed_718_ = lean_unbox(v_t_715_);
v_res_719_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(v_motive_714_, v_t_boxed_718_, v_h_716_, v_compoundAtomicIfFlattened_717_);
lean_dec(v_compoundAtomicIfFlattened_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(lean_object* v_nonAtomic_720_){
_start:
{
lean_inc(v_nonAtomic_720_);
return v_nonAtomic_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg___boxed(lean_object* v_nonAtomic_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(v_nonAtomic_721_);
lean_dec(v_nonAtomic_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(lean_object* v_motive_723_, uint8_t v_t_724_, lean_object* v_h_725_, lean_object* v_nonAtomic_726_){
_start:
{
lean_inc(v_nonAtomic_726_);
return v_nonAtomic_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___boxed(lean_object* v_motive_727_, lean_object* v_t_728_, lean_object* v_h_729_, lean_object* v_nonAtomic_730_){
_start:
{
uint8_t v_t_boxed_731_; lean_object* v_res_732_; 
v_t_boxed_731_ = lean_unbox(v_t_728_);
v_res_732_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(v_motive_727_, v_t_boxed_731_, v_h_729_, v_nonAtomic_730_);
lean_dec(v_nonAtomic_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0(uint8_t v_x_733_){
_start:
{
switch(v_x_733_)
{
case 0:
{
lean_object* v___x_734_; 
v___x_734_ = lean_unsigned_to_nat(0u);
return v___x_734_;
}
case 1:
{
lean_object* v___x_735_; 
v___x_735_ = lean_unsigned_to_nat(1u);
return v___x_735_;
}
case 2:
{
lean_object* v___x_736_; 
v___x_736_ = lean_unsigned_to_nat(2u);
return v___x_736_;
}
case 3:
{
lean_object* v___x_737_; 
v___x_737_ = lean_unsigned_to_nat(3u);
return v___x_737_;
}
default: 
{
lean_object* v___x_738_; 
v___x_738_ = lean_unsigned_to_nat(4u);
return v___x_738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0___boxed(lean_object* v_x_739_){
_start:
{
uint8_t v_x_104__boxed_740_; lean_object* v_res_741_; 
v_x_104__boxed_740_ = lean_unbox(v_x_739_);
v_res_741_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_x_104__boxed_740_);
return v_res_741_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_Atomicness_max(uint8_t v_e1_742_, uint8_t v_e2_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e2_743_);
v___x_745_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e1_742_);
v___x_746_ = lean_nat_dec_le(v___x_744_, v___x_745_);
lean_dec(v___x_745_);
lean_dec(v___x_744_);
if (v___x_746_ == 0)
{
return v_e2_743_;
}
else
{
return v_e1_742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___boxed(lean_object* v_e1_747_, lean_object* v_e2_748_){
_start:
{
uint8_t v_e1_boxed_749_; uint8_t v_e2_boxed_750_; uint8_t v_res_751_; lean_object* v_r_752_; 
v_e1_boxed_749_ = lean_unbox(v_e1_747_);
v_e2_boxed_750_ = lean_unbox(v_e2_748_);
v_res_751_ = l_Lean_Fmt_Doc_Atomicness_max(v_e1_boxed_749_, v_e2_boxed_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0(lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = ((lean_object*)(l_Lean_Fmt_instReprAssertion___lam__0___closed__1));
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0___boxed(lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Fmt_instReprAssertion___lam__0(v_x_759_, v_x_760_);
lean_dec(v_x_760_);
lean_dec_ref(v_x_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg(lean_object* v_x_764_){
_start:
{
switch(lean_obj_tag(v_x_764_))
{
case 0:
{
lean_object* v___x_765_; 
v___x_765_ = lean_unsigned_to_nat(0u);
return v___x_765_;
}
case 1:
{
lean_object* v___x_766_; 
v___x_766_ = lean_unsigned_to_nat(1u);
return v___x_766_;
}
case 2:
{
lean_object* v___x_767_; 
v___x_767_ = lean_unsigned_to_nat(2u);
return v___x_767_;
}
case 3:
{
lean_object* v___x_768_; 
v___x_768_ = lean_unsigned_to_nat(3u);
return v___x_768_;
}
case 4:
{
lean_object* v___x_769_; 
v___x_769_ = lean_unsigned_to_nat(4u);
return v___x_769_;
}
case 5:
{
lean_object* v___x_770_; 
v___x_770_ = lean_unsigned_to_nat(5u);
return v___x_770_;
}
case 6:
{
lean_object* v___x_771_; 
v___x_771_ = lean_unsigned_to_nat(6u);
return v___x_771_;
}
case 7:
{
lean_object* v___x_772_; 
v___x_772_ = lean_unsigned_to_nat(7u);
return v___x_772_;
}
case 8:
{
lean_object* v___x_773_; 
v___x_773_ = lean_unsigned_to_nat(8u);
return v___x_773_;
}
case 9:
{
lean_object* v___x_774_; 
v___x_774_ = lean_unsigned_to_nat(9u);
return v___x_774_;
}
case 10:
{
lean_object* v___x_775_; 
v___x_775_ = lean_unsigned_to_nat(10u);
return v___x_775_;
}
case 11:
{
lean_object* v___x_776_; 
v___x_776_ = lean_unsigned_to_nat(11u);
return v___x_776_;
}
case 12:
{
lean_object* v___x_777_; 
v___x_777_ = lean_unsigned_to_nat(12u);
return v___x_777_;
}
case 13:
{
lean_object* v___x_778_; 
v___x_778_ = lean_unsigned_to_nat(13u);
return v___x_778_;
}
case 14:
{
lean_object* v___x_779_; 
v___x_779_ = lean_unsigned_to_nat(14u);
return v___x_779_;
}
default: 
{
lean_object* v___x_780_; 
v___x_780_ = lean_unsigned_to_nat(15u);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg___boxed(lean_object* v_x_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Fmt_Doc_ctorIdx___redArg(v_x_781_);
lean_dec(v_x_781_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx(lean_object* v_00_u03c4_783_, lean_object* v_x_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Fmt_Doc_ctorIdx___redArg(v_x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___boxed(lean_object* v_00_u03c4_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Fmt_Doc_ctorIdx(v_00_u03c4_786_, v_x_787_);
lean_dec(v_x_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___redArg(lean_object* v_t_789_, lean_object* v_k_790_){
_start:
{
switch(lean_obj_tag(v_t_789_))
{
case 0:
{
return v_k_790_;
}
case 1:
{
lean_object* v_f_791_; lean_object* v___x_792_; 
v_f_791_ = lean_ctor_get(v_t_789_, 0);
lean_inc_ref(v_f_791_);
lean_dec_ref_known(v_t_789_, 1);
v___x_792_ = lean_apply_1(v_k_790_, v_f_791_);
return v___x_792_;
}
case 2:
{
lean_object* v_s_793_; lean_object* v___x_794_; 
v_s_793_ = lean_ctor_get(v_t_789_, 0);
lean_inc_ref(v_s_793_);
lean_dec_ref_known(v_t_789_, 1);
v___x_794_ = lean_apply_1(v_k_790_, v_s_793_);
return v___x_794_;
}
case 3:
{
lean_object* v_id_795_; lean_object* v_d_796_; lean_object* v___x_797_; 
v_id_795_ = lean_ctor_get(v_t_789_, 0);
lean_inc(v_id_795_);
v_d_796_ = lean_ctor_get(v_t_789_, 1);
lean_inc(v_d_796_);
lean_dec_ref_known(v_t_789_, 2);
v___x_797_ = lean_apply_2(v_k_790_, v_id_795_, v_d_796_);
return v___x_797_;
}
case 6:
{
lean_object* v_n_798_; uint8_t v_isCumulative_799_; lean_object* v_d_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_n_798_ = lean_ctor_get(v_t_789_, 0);
lean_inc(v_n_798_);
v_isCumulative_799_ = lean_ctor_get_uint8(v_t_789_, sizeof(void*)*2);
v_d_800_ = lean_ctor_get(v_t_789_, 1);
lean_inc(v_d_800_);
lean_dec_ref_known(v_t_789_, 2);
v___x_801_ = lean_box(v_isCumulative_799_);
v___x_802_ = lean_apply_3(v_k_790_, v_n_798_, v___x_801_, v_d_800_);
return v___x_802_;
}
case 8:
{
uint8_t v_onlyNonCumulative_803_; lean_object* v_d_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_onlyNonCumulative_803_ = lean_ctor_get_uint8(v_t_789_, sizeof(void*)*1);
v_d_804_ = lean_ctor_get(v_t_789_, 0);
lean_inc(v_d_804_);
lean_dec_ref_known(v_t_789_, 1);
v___x_805_ = lean_box(v_onlyNonCumulative_803_);
v___x_806_ = lean_apply_2(v_k_790_, v___x_805_, v_d_804_);
return v___x_806_;
}
case 12:
{
lean_object* v_p_807_; lean_object* v_d_808_; lean_object* v___x_809_; 
v_p_807_ = lean_ctor_get(v_t_789_, 0);
lean_inc_ref(v_p_807_);
v_d_808_ = lean_ctor_get(v_t_789_, 1);
lean_inc(v_d_808_);
lean_dec_ref_known(v_t_789_, 2);
v___x_809_ = lean_apply_2(v_k_790_, v_p_807_, v_d_808_);
return v___x_809_;
}
case 13:
{
lean_object* v_cost_810_; lean_object* v_d_811_; lean_object* v___x_812_; 
v_cost_810_ = lean_ctor_get(v_t_789_, 0);
lean_inc(v_cost_810_);
v_d_811_ = lean_ctor_get(v_t_789_, 1);
lean_inc(v_d_811_);
lean_dec_ref_known(v_t_789_, 2);
v___x_812_ = lean_apply_2(v_k_790_, v_cost_810_, v_d_811_);
return v___x_812_;
}
case 14:
{
lean_object* v_a_813_; lean_object* v_b_814_; lean_object* v___x_815_; 
v_a_813_ = lean_ctor_get(v_t_789_, 0);
lean_inc(v_a_813_);
v_b_814_ = lean_ctor_get(v_t_789_, 1);
lean_inc(v_b_814_);
lean_dec_ref_known(v_t_789_, 2);
v___x_815_ = lean_apply_2(v_k_790_, v_a_813_, v_b_814_);
return v___x_815_;
}
case 15:
{
lean_object* v_a_816_; lean_object* v_b_817_; lean_object* v___x_818_; 
v_a_816_ = lean_ctor_get(v_t_789_, 0);
lean_inc(v_a_816_);
v_b_817_ = lean_ctor_get(v_t_789_, 1);
lean_inc(v_b_817_);
lean_dec_ref_known(v_t_789_, 2);
v___x_818_ = lean_apply_2(v_k_790_, v_a_816_, v_b_817_);
return v___x_818_;
}
default: 
{
lean_object* v_d_819_; lean_object* v___x_820_; 
v_d_819_ = lean_ctor_get(v_t_789_, 0);
lean_inc(v_d_819_);
lean_dec(v_t_789_);
v___x_820_ = lean_apply_1(v_k_790_, v_d_819_);
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim(lean_object* v_00_u03c4_821_, lean_object* v_motive_822_, lean_object* v_ctorIdx_823_, lean_object* v_t_824_, lean_object* v_h_825_, lean_object* v_k_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_824_, v_k_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___boxed(lean_object* v_00_u03c4_828_, lean_object* v_motive_829_, lean_object* v_ctorIdx_830_, lean_object* v_t_831_, lean_object* v_h_832_, lean_object* v_k_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Fmt_Doc_ctorElim(v_00_u03c4_828_, v_motive_829_, v_ctorIdx_830_, v_t_831_, v_h_832_, v_k_833_);
lean_dec(v_ctorIdx_830_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim___redArg(lean_object* v_t_835_, lean_object* v_failure_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_835_, v_failure_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim(lean_object* v_00_u03c4_838_, lean_object* v_motive_839_, lean_object* v_t_840_, lean_object* v_h_841_, lean_object* v_failure_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_840_, v_failure_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim___redArg(lean_object* v_t_844_, lean_object* v_newline_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_844_, v_newline_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim(lean_object* v_00_u03c4_847_, lean_object* v_motive_848_, lean_object* v_t_849_, lean_object* v_h_850_, lean_object* v_newline_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_849_, v_newline_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim___redArg(lean_object* v_t_853_, lean_object* v_text_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_853_, v_text_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim(lean_object* v_00_u03c4_856_, lean_object* v_motive_857_, lean_object* v_t_858_, lean_object* v_h_859_, lean_object* v_text_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_858_, v_text_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim___redArg(lean_object* v_t_862_, lean_object* v_tagged_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_862_, v_tagged_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim(lean_object* v_00_u03c4_865_, lean_object* v_motive_866_, lean_object* v_t_867_, lean_object* v_h_868_, lean_object* v_tagged_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_867_, v_tagged_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim___redArg(lean_object* v_t_871_, lean_object* v_flattened_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_871_, v_flattened_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim(lean_object* v_00_u03c4_874_, lean_object* v_motive_875_, lean_object* v_t_876_, lean_object* v_h_877_, lean_object* v_flattened_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_876_, v_flattened_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim___redArg(lean_object* v_t_880_, lean_object* v_unflattenable_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_880_, v_unflattenable_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim(lean_object* v_00_u03c4_883_, lean_object* v_motive_884_, lean_object* v_t_885_, lean_object* v_h_886_, lean_object* v_unflattenable_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_885_, v_unflattenable_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim___redArg(lean_object* v_t_889_, lean_object* v_indented_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_889_, v_indented_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim(lean_object* v_00_u03c4_892_, lean_object* v_motive_893_, lean_object* v_t_894_, lean_object* v_h_895_, lean_object* v_indented_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_894_, v_indented_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim___redArg(lean_object* v_t_898_, lean_object* v_aligned_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_898_, v_aligned_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim(lean_object* v_00_u03c4_901_, lean_object* v_motive_902_, lean_object* v_t_903_, lean_object* v_h_904_, lean_object* v_aligned_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_903_, v_aligned_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim___redArg(lean_object* v_t_907_, lean_object* v_unindented_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_907_, v_unindented_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim(lean_object* v_00_u03c4_910_, lean_object* v_motive_911_, lean_object* v_t_912_, lean_object* v_h_913_, lean_object* v_unindented_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_912_, v_unindented_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim___redArg(lean_object* v_t_916_, lean_object* v_final_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_916_, v_final_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim(lean_object* v_00_u03c4_919_, lean_object* v_motive_920_, lean_object* v_t_921_, lean_object* v_h_922_, lean_object* v_final_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_921_, v_final_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim___redArg(lean_object* v_t_925_, lean_object* v_initial_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_925_, v_initial_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim(lean_object* v_00_u03c4_928_, lean_object* v_motive_929_, lean_object* v_t_930_, lean_object* v_h_931_, lean_object* v_initial_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_930_, v_initial_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim___redArg(lean_object* v_t_934_, lean_object* v_free_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_934_, v_free_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim(lean_object* v_00_u03c4_937_, lean_object* v_motive_938_, lean_object* v_t_939_, lean_object* v_h_940_, lean_object* v_free_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_939_, v_free_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim___redArg(lean_object* v_t_943_, lean_object* v_guarded_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_943_, v_guarded_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim(lean_object* v_00_u03c4_946_, lean_object* v_motive_947_, lean_object* v_t_948_, lean_object* v_h_949_, lean_object* v_guarded_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_948_, v_guarded_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim___redArg(lean_object* v_t_952_, lean_object* v_costing_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_952_, v_costing_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim(lean_object* v_00_u03c4_955_, lean_object* v_motive_956_, lean_object* v_t_957_, lean_object* v_h_958_, lean_object* v_costing_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_957_, v_costing_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim___redArg(lean_object* v_t_961_, lean_object* v_either_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_961_, v_either_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim(lean_object* v_00_u03c4_964_, lean_object* v_motive_965_, lean_object* v_t_966_, lean_object* v_h_967_, lean_object* v_either_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_966_, v_either_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim___redArg(lean_object* v_t_970_, lean_object* v_append_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_970_, v_append_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim(lean_object* v_00_u03c4_973_, lean_object* v_motive_974_, lean_object* v_t_975_, lean_object* v_h_976_, lean_object* v_append_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_975_, v_append_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg(lean_object* v_x_979_, lean_object* v_h__1_980_, lean_object* v_h__2_981_, lean_object* v_h__3_982_, lean_object* v_h__4_983_, lean_object* v_h__5_984_, lean_object* v_h__6_985_, lean_object* v_h__7_986_, lean_object* v_h__8_987_, lean_object* v_h__9_988_, lean_object* v_h__10_989_, lean_object* v_h__11_990_, lean_object* v_h__12_991_, lean_object* v_h__13_992_, lean_object* v_h__14_993_, lean_object* v_h__15_994_, lean_object* v_h__16_995_){
_start:
{
switch(lean_obj_tag(v_x_979_))
{
case 0:
{
lean_object* v___x_996_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
v___x_996_ = lean_apply_1(v_h__1_980_, lean_box(0));
return v___x_996_;
}
case 1:
{
lean_object* v_f_997_; lean_object* v___x_998_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__1_980_);
v_f_997_ = lean_ctor_get(v_x_979_, 0);
lean_inc_ref(v_f_997_);
lean_dec_ref_known(v_x_979_, 1);
v___x_998_ = lean_apply_2(v_h__2_981_, lean_box(0), v_f_997_);
return v___x_998_;
}
case 2:
{
lean_object* v_s_999_; lean_object* v___x_1000_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_s_999_ = lean_ctor_get(v_x_979_, 0);
lean_inc_ref(v_s_999_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1000_ = lean_apply_2(v_h__3_982_, lean_box(0), v_s_999_);
return v___x_1000_;
}
case 3:
{
lean_object* v_id_1001_; lean_object* v_d_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_id_1001_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_id_1001_);
v_d_1002_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_d_1002_);
lean_dec_ref_known(v_x_979_, 2);
v___x_1003_ = lean_apply_3(v_h__7_986_, lean_box(0), v_id_1001_, v_d_1002_);
return v___x_1003_;
}
case 4:
{
lean_object* v_d_1004_; lean_object* v___x_1005_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_d_1004_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_d_1004_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1005_ = lean_apply_2(v_h__4_983_, lean_box(0), v_d_1004_);
return v___x_1005_;
}
case 5:
{
lean_object* v_d_1006_; lean_object* v___x_1007_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_d_1006_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_d_1006_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1007_ = lean_apply_2(v_h__5_984_, lean_box(0), v_d_1006_);
return v___x_1007_;
}
case 6:
{
lean_object* v_n_1008_; uint8_t v_isCumulative_1009_; lean_object* v_d_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_n_1008_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_n_1008_);
v_isCumulative_1009_ = lean_ctor_get_uint8(v_x_979_, sizeof(void*)*2);
v_d_1010_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_d_1010_);
lean_dec_ref_known(v_x_979_, 2);
v___x_1011_ = lean_box(v_isCumulative_1009_);
v___x_1012_ = lean_apply_4(v_h__8_987_, lean_box(0), v_n_1008_, v___x_1011_, v_d_1010_);
return v___x_1012_;
}
case 7:
{
lean_object* v_d_1013_; lean_object* v___x_1014_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_d_1013_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_d_1013_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1014_ = lean_apply_2(v_h__9_988_, lean_box(0), v_d_1013_);
return v___x_1014_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1015_; lean_object* v_d_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_onlyNonCumulative_1015_ = lean_ctor_get_uint8(v_x_979_, sizeof(void*)*1);
v_d_1016_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_d_1016_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1017_ = lean_box(v_onlyNonCumulative_1015_);
v___x_1018_ = lean_apply_3(v_h__10_989_, lean_box(0), v___x_1017_, v_d_1016_);
return v___x_1018_;
}
case 9:
{
lean_object* v_d_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_d_1019_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_d_1019_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1020_ = lean_apply_2(v_h__13_992_, lean_box(0), v_d_1019_);
return v___x_1020_;
}
case 10:
{
lean_object* v_d_1021_; lean_object* v___x_1022_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_d_1021_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_d_1021_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1022_ = lean_apply_2(v_h__14_993_, lean_box(0), v_d_1021_);
return v___x_1022_;
}
case 11:
{
lean_object* v_d_1023_; lean_object* v___x_1024_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_d_1023_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_d_1023_);
lean_dec_ref_known(v_x_979_, 1);
v___x_1024_ = lean_apply_2(v_h__11_990_, lean_box(0), v_d_1023_);
return v___x_1024_;
}
case 12:
{
lean_object* v_p_1025_; lean_object* v_d_1026_; lean_object* v___x_1027_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_p_1025_ = lean_ctor_get(v_x_979_, 0);
lean_inc_ref(v_p_1025_);
v_d_1026_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_d_1026_);
lean_dec_ref_known(v_x_979_, 2);
v___x_1027_ = lean_apply_3(v_h__6_985_, lean_box(0), v_p_1025_, v_d_1026_);
return v___x_1027_;
}
case 13:
{
lean_object* v_cost_1028_; lean_object* v_d_1029_; lean_object* v___x_1030_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_cost_1028_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_cost_1028_);
v_d_1029_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_d_1029_);
lean_dec_ref_known(v_x_979_, 2);
v___x_1030_ = lean_apply_3(v_h__12_991_, lean_box(0), v_cost_1028_, v_d_1029_);
return v___x_1030_;
}
case 14:
{
lean_object* v_a_1031_; lean_object* v_b_1032_; lean_object* v___x_1033_; 
lean_dec(v_h__16_995_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_a_1031_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_a_1031_);
v_b_1032_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_b_1032_);
lean_dec_ref_known(v_x_979_, 2);
v___x_1033_ = lean_apply_3(v_h__15_994_, lean_box(0), v_a_1031_, v_b_1032_);
return v___x_1033_;
}
default: 
{
lean_object* v_a_1034_; lean_object* v_b_1035_; lean_object* v___x_1036_; 
lean_dec(v_h__15_994_);
lean_dec(v_h__14_993_);
lean_dec(v_h__13_992_);
lean_dec(v_h__12_991_);
lean_dec(v_h__11_990_);
lean_dec(v_h__10_989_);
lean_dec(v_h__9_988_);
lean_dec(v_h__8_987_);
lean_dec(v_h__7_986_);
lean_dec(v_h__6_985_);
lean_dec(v_h__5_984_);
lean_dec(v_h__4_983_);
lean_dec(v_h__3_982_);
lean_dec(v_h__2_981_);
lean_dec(v_h__1_980_);
v_a_1034_ = lean_ctor_get(v_x_979_, 0);
lean_inc(v_a_1034_);
v_b_1035_ = lean_ctor_get(v_x_979_, 1);
lean_inc(v_b_1035_);
lean_dec_ref_known(v_x_979_, 2);
v___x_1036_ = lean_apply_3(v_h__16_995_, lean_box(0), v_a_1034_, v_b_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1037_ = _args[0];
lean_object* v_h__1_1038_ = _args[1];
lean_object* v_h__2_1039_ = _args[2];
lean_object* v_h__3_1040_ = _args[3];
lean_object* v_h__4_1041_ = _args[4];
lean_object* v_h__5_1042_ = _args[5];
lean_object* v_h__6_1043_ = _args[6];
lean_object* v_h__7_1044_ = _args[7];
lean_object* v_h__8_1045_ = _args[8];
lean_object* v_h__9_1046_ = _args[9];
lean_object* v_h__10_1047_ = _args[10];
lean_object* v_h__11_1048_ = _args[11];
lean_object* v_h__12_1049_ = _args[12];
lean_object* v_h__13_1050_ = _args[13];
lean_object* v_h__14_1051_ = _args[14];
lean_object* v_h__15_1052_ = _args[15];
lean_object* v_h__16_1053_ = _args[16];
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___redArg(v_x_1037_, v_h__1_1038_, v_h__2_1039_, v_h__3_1040_, v_h__4_1041_, v_h__5_1042_, v_h__6_1043_, v_h__7_1044_, v_h__8_1045_, v_h__9_1046_, v_h__10_1047_, v_h__11_1048_, v_h__12_1049_, v_h__13_1050_, v_h__14_1051_, v_h__15_1052_, v_h__16_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter(lean_object* v_motive_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_h__1_1058_, lean_object* v_h__2_1059_, lean_object* v_h__3_1060_, lean_object* v_h__4_1061_, lean_object* v_h__5_1062_, lean_object* v_h__6_1063_, lean_object* v_h__7_1064_, lean_object* v_h__8_1065_, lean_object* v_h__9_1066_, lean_object* v_h__10_1067_, lean_object* v_h__11_1068_, lean_object* v_h__12_1069_, lean_object* v_h__13_1070_, lean_object* v_h__14_1071_, lean_object* v_h__15_1072_, lean_object* v_h__16_1073_){
_start:
{
switch(lean_obj_tag(v_x_1057_))
{
case 0:
{
lean_object* v___x_1074_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
v___x_1074_ = lean_apply_1(v_h__1_1058_, lean_box(0));
return v___x_1074_;
}
case 1:
{
lean_object* v_f_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__1_1058_);
v_f_1075_ = lean_ctor_get(v_x_1057_, 0);
lean_inc_ref(v_f_1075_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1076_ = lean_apply_2(v_h__2_1059_, lean_box(0), v_f_1075_);
return v___x_1076_;
}
case 2:
{
lean_object* v_s_1077_; lean_object* v___x_1078_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_s_1077_ = lean_ctor_get(v_x_1057_, 0);
lean_inc_ref(v_s_1077_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1078_ = lean_apply_2(v_h__3_1060_, lean_box(0), v_s_1077_);
return v___x_1078_;
}
case 3:
{
lean_object* v_id_1079_; lean_object* v_d_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_id_1079_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_id_1079_);
v_d_1080_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_d_1080_);
lean_dec_ref_known(v_x_1057_, 2);
v___x_1081_ = lean_apply_3(v_h__7_1064_, lean_box(0), v_id_1079_, v_d_1080_);
return v___x_1081_;
}
case 4:
{
lean_object* v_d_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_d_1082_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_d_1082_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1083_ = lean_apply_2(v_h__4_1061_, lean_box(0), v_d_1082_);
return v___x_1083_;
}
case 5:
{
lean_object* v_d_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_d_1084_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_d_1084_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1085_ = lean_apply_2(v_h__5_1062_, lean_box(0), v_d_1084_);
return v___x_1085_;
}
case 6:
{
lean_object* v_n_1086_; uint8_t v_isCumulative_1087_; lean_object* v_d_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_n_1086_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_n_1086_);
v_isCumulative_1087_ = lean_ctor_get_uint8(v_x_1057_, sizeof(void*)*2);
v_d_1088_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_d_1088_);
lean_dec_ref_known(v_x_1057_, 2);
v___x_1089_ = lean_box(v_isCumulative_1087_);
v___x_1090_ = lean_apply_4(v_h__8_1065_, lean_box(0), v_n_1086_, v___x_1089_, v_d_1088_);
return v___x_1090_;
}
case 7:
{
lean_object* v_d_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_d_1091_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_d_1091_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1092_ = lean_apply_2(v_h__9_1066_, lean_box(0), v_d_1091_);
return v___x_1092_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1093_; lean_object* v_d_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_onlyNonCumulative_1093_ = lean_ctor_get_uint8(v_x_1057_, sizeof(void*)*1);
v_d_1094_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_d_1094_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1095_ = lean_box(v_onlyNonCumulative_1093_);
v___x_1096_ = lean_apply_3(v_h__10_1067_, lean_box(0), v___x_1095_, v_d_1094_);
return v___x_1096_;
}
case 9:
{
lean_object* v_d_1097_; lean_object* v___x_1098_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_d_1097_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_d_1097_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1098_ = lean_apply_2(v_h__13_1070_, lean_box(0), v_d_1097_);
return v___x_1098_;
}
case 10:
{
lean_object* v_d_1099_; lean_object* v___x_1100_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_d_1099_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_d_1099_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1100_ = lean_apply_2(v_h__14_1071_, lean_box(0), v_d_1099_);
return v___x_1100_;
}
case 11:
{
lean_object* v_d_1101_; lean_object* v___x_1102_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_d_1101_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_d_1101_);
lean_dec_ref_known(v_x_1057_, 1);
v___x_1102_ = lean_apply_2(v_h__11_1068_, lean_box(0), v_d_1101_);
return v___x_1102_;
}
case 12:
{
lean_object* v_p_1103_; lean_object* v_d_1104_; lean_object* v___x_1105_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_p_1103_ = lean_ctor_get(v_x_1057_, 0);
lean_inc_ref(v_p_1103_);
v_d_1104_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_d_1104_);
lean_dec_ref_known(v_x_1057_, 2);
v___x_1105_ = lean_apply_3(v_h__6_1063_, lean_box(0), v_p_1103_, v_d_1104_);
return v___x_1105_;
}
case 13:
{
lean_object* v_cost_1106_; lean_object* v_d_1107_; lean_object* v___x_1108_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_cost_1106_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_cost_1106_);
v_d_1107_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_d_1107_);
lean_dec_ref_known(v_x_1057_, 2);
v___x_1108_ = lean_apply_3(v_h__12_1069_, lean_box(0), v_cost_1106_, v_d_1107_);
return v___x_1108_;
}
case 14:
{
lean_object* v_a_1109_; lean_object* v_b_1110_; lean_object* v___x_1111_; 
lean_dec(v_h__16_1073_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_a_1109_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_a_1109_);
v_b_1110_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_b_1110_);
lean_dec_ref_known(v_x_1057_, 2);
v___x_1111_ = lean_apply_3(v_h__15_1072_, lean_box(0), v_a_1109_, v_b_1110_);
return v___x_1111_;
}
default: 
{
lean_object* v_a_1112_; lean_object* v_b_1113_; lean_object* v___x_1114_; 
lean_dec(v_h__15_1072_);
lean_dec(v_h__14_1071_);
lean_dec(v_h__13_1070_);
lean_dec(v_h__12_1069_);
lean_dec(v_h__11_1068_);
lean_dec(v_h__10_1067_);
lean_dec(v_h__9_1066_);
lean_dec(v_h__8_1065_);
lean_dec(v_h__7_1064_);
lean_dec(v_h__6_1063_);
lean_dec(v_h__5_1062_);
lean_dec(v_h__4_1061_);
lean_dec(v_h__3_1060_);
lean_dec(v_h__2_1059_);
lean_dec(v_h__1_1058_);
v_a_1112_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_a_1112_);
v_b_1113_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_b_1113_);
lean_dec_ref_known(v_x_1057_, 2);
v___x_1114_ = lean_apply_3(v_h__16_1073_, lean_box(0), v_a_1112_, v_b_1113_);
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter___boxed(lean_object** _args){
lean_object* v_motive_1115_ = _args[0];
lean_object* v_x_1116_ = _args[1];
lean_object* v_x_1117_ = _args[2];
lean_object* v_h__1_1118_ = _args[3];
lean_object* v_h__2_1119_ = _args[4];
lean_object* v_h__3_1120_ = _args[5];
lean_object* v_h__4_1121_ = _args[6];
lean_object* v_h__5_1122_ = _args[7];
lean_object* v_h__6_1123_ = _args[8];
lean_object* v_h__7_1124_ = _args[9];
lean_object* v_h__8_1125_ = _args[10];
lean_object* v_h__9_1126_ = _args[11];
lean_object* v_h__10_1127_ = _args[12];
lean_object* v_h__11_1128_ = _args[13];
lean_object* v_h__12_1129_ = _args[14];
lean_object* v_h__13_1130_ = _args[15];
lean_object* v_h__14_1131_ = _args[16];
lean_object* v_h__15_1132_ = _args[17];
lean_object* v_h__16_1133_ = _args[18];
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_failureSet_match__1_splitter(v_motive_1115_, v_x_1116_, v_x_1117_, v_h__1_1118_, v_h__2_1119_, v_h__3_1120_, v_h__4_1121_, v_h__5_1122_, v_h__6_1123_, v_h__7_1124_, v_h__8_1125_, v_h__9_1126_, v_h__10_1127_, v_h__11_1128_, v_h__12_1129_, v_h__13_1130_, v_h__14_1131_, v_h__15_1132_, v_h__16_1133_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(lean_object* v_x_1135_, lean_object* v_h__1_1136_, lean_object* v_h__2_1137_, lean_object* v_h__3_1138_, lean_object* v_h__4_1139_, lean_object* v_h__5_1140_, lean_object* v_h__6_1141_, lean_object* v_h__7_1142_, lean_object* v_h__8_1143_, lean_object* v_h__9_1144_, lean_object* v_h__10_1145_, lean_object* v_h__11_1146_, lean_object* v_h__12_1147_, lean_object* v_h__13_1148_, lean_object* v_h__14_1149_, lean_object* v_h__15_1150_, lean_object* v_h__16_1151_){
_start:
{
switch(lean_obj_tag(v_x_1135_))
{
case 0:
{
lean_object* v___x_1152_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
v___x_1152_ = lean_apply_1(v_h__1_1136_, lean_box(0));
return v___x_1152_;
}
case 1:
{
lean_object* v_f_1153_; lean_object* v___x_1154_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__1_1136_);
v_f_1153_ = lean_ctor_get(v_x_1135_, 0);
lean_inc_ref(v_f_1153_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1154_ = lean_apply_2(v_h__2_1137_, lean_box(0), v_f_1153_);
return v___x_1154_;
}
case 2:
{
lean_object* v_s_1155_; lean_object* v___x_1156_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_s_1155_ = lean_ctor_get(v_x_1135_, 0);
lean_inc_ref(v_s_1155_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1156_ = lean_apply_2(v_h__3_1138_, lean_box(0), v_s_1155_);
return v___x_1156_;
}
case 3:
{
lean_object* v_id_1157_; lean_object* v_d_1158_; lean_object* v___x_1159_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_id_1157_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_id_1157_);
v_d_1158_ = lean_ctor_get(v_x_1135_, 1);
lean_inc(v_d_1158_);
lean_dec_ref_known(v_x_1135_, 2);
v___x_1159_ = lean_apply_3(v_h__5_1140_, lean_box(0), v_id_1157_, v_d_1158_);
return v___x_1159_;
}
case 4:
{
lean_object* v_d_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_d_1160_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_d_1160_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1161_ = lean_apply_2(v_h__4_1139_, lean_box(0), v_d_1160_);
return v___x_1161_;
}
case 5:
{
lean_object* v_d_1162_; lean_object* v___x_1163_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_d_1162_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_d_1162_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1163_ = lean_apply_2(v_h__12_1147_, lean_box(0), v_d_1162_);
return v___x_1163_;
}
case 6:
{
lean_object* v_n_1164_; uint8_t v_isCumulative_1165_; lean_object* v_d_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_n_1164_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_n_1164_);
v_isCumulative_1165_ = lean_ctor_get_uint8(v_x_1135_, sizeof(void*)*2);
v_d_1166_ = lean_ctor_get(v_x_1135_, 1);
lean_inc(v_d_1166_);
lean_dec_ref_known(v_x_1135_, 2);
v___x_1167_ = lean_box(v_isCumulative_1165_);
v___x_1168_ = lean_apply_4(v_h__6_1141_, lean_box(0), v_n_1164_, v___x_1167_, v_d_1166_);
return v___x_1168_;
}
case 7:
{
lean_object* v_d_1169_; lean_object* v___x_1170_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_d_1169_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_d_1169_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1170_ = lean_apply_2(v_h__7_1142_, lean_box(0), v_d_1169_);
return v___x_1170_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1171_; lean_object* v_d_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_onlyNonCumulative_1171_ = lean_ctor_get_uint8(v_x_1135_, sizeof(void*)*1);
v_d_1172_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_d_1172_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1173_ = lean_box(v_onlyNonCumulative_1171_);
v___x_1174_ = lean_apply_3(v_h__8_1143_, lean_box(0), v___x_1173_, v_d_1172_);
return v___x_1174_;
}
case 9:
{
lean_object* v_d_1175_; lean_object* v___x_1176_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_d_1175_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_d_1175_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1176_ = lean_apply_2(v_h__9_1144_, lean_box(0), v_d_1175_);
return v___x_1176_;
}
case 10:
{
lean_object* v_d_1177_; lean_object* v___x_1178_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_d_1177_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_d_1177_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1178_ = lean_apply_2(v_h__10_1145_, lean_box(0), v_d_1177_);
return v___x_1178_;
}
case 11:
{
lean_object* v_d_1179_; lean_object* v___x_1180_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_d_1179_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_d_1179_);
lean_dec_ref_known(v_x_1135_, 1);
v___x_1180_ = lean_apply_2(v_h__11_1146_, lean_box(0), v_d_1179_);
return v___x_1180_;
}
case 12:
{
lean_object* v_p_1181_; lean_object* v_d_1182_; lean_object* v___x_1183_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_p_1181_ = lean_ctor_get(v_x_1135_, 0);
lean_inc_ref(v_p_1181_);
v_d_1182_ = lean_ctor_get(v_x_1135_, 1);
lean_inc(v_d_1182_);
lean_dec_ref_known(v_x_1135_, 2);
v___x_1183_ = lean_apply_3(v_h__13_1148_, lean_box(0), v_p_1181_, v_d_1182_);
return v___x_1183_;
}
case 13:
{
lean_object* v_cost_1184_; lean_object* v_d_1185_; lean_object* v___x_1186_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__15_1150_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_cost_1184_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_cost_1184_);
v_d_1185_ = lean_ctor_get(v_x_1135_, 1);
lean_inc(v_d_1185_);
lean_dec_ref_known(v_x_1135_, 2);
v___x_1186_ = lean_apply_3(v_h__14_1149_, lean_box(0), v_cost_1184_, v_d_1185_);
return v___x_1186_;
}
case 14:
{
lean_object* v_a_1187_; lean_object* v_b_1188_; lean_object* v___x_1189_; 
lean_dec(v_h__16_1151_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_a_1187_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_a_1187_);
v_b_1188_ = lean_ctor_get(v_x_1135_, 1);
lean_inc(v_b_1188_);
lean_dec_ref_known(v_x_1135_, 2);
v___x_1189_ = lean_apply_3(v_h__15_1150_, lean_box(0), v_a_1187_, v_b_1188_);
return v___x_1189_;
}
default: 
{
lean_object* v_a_1190_; lean_object* v_b_1191_; lean_object* v___x_1192_; 
lean_dec(v_h__15_1150_);
lean_dec(v_h__14_1149_);
lean_dec(v_h__13_1148_);
lean_dec(v_h__12_1147_);
lean_dec(v_h__11_1146_);
lean_dec(v_h__10_1145_);
lean_dec(v_h__9_1144_);
lean_dec(v_h__8_1143_);
lean_dec(v_h__7_1142_);
lean_dec(v_h__6_1141_);
lean_dec(v_h__5_1140_);
lean_dec(v_h__4_1139_);
lean_dec(v_h__3_1138_);
lean_dec(v_h__2_1137_);
lean_dec(v_h__1_1136_);
v_a_1190_ = lean_ctor_get(v_x_1135_, 0);
lean_inc(v_a_1190_);
v_b_1191_ = lean_ctor_get(v_x_1135_, 1);
lean_inc(v_b_1191_);
lean_dec_ref_known(v_x_1135_, 2);
v___x_1192_ = lean_apply_3(v_h__16_1151_, lean_box(0), v_a_1190_, v_b_1191_);
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1193_ = _args[0];
lean_object* v_h__1_1194_ = _args[1];
lean_object* v_h__2_1195_ = _args[2];
lean_object* v_h__3_1196_ = _args[3];
lean_object* v_h__4_1197_ = _args[4];
lean_object* v_h__5_1198_ = _args[5];
lean_object* v_h__6_1199_ = _args[6];
lean_object* v_h__7_1200_ = _args[7];
lean_object* v_h__8_1201_ = _args[8];
lean_object* v_h__9_1202_ = _args[9];
lean_object* v_h__10_1203_ = _args[10];
lean_object* v_h__11_1204_ = _args[11];
lean_object* v_h__12_1205_ = _args[12];
lean_object* v_h__13_1206_ = _args[13];
lean_object* v_h__14_1207_ = _args[14];
lean_object* v_h__15_1208_ = _args[15];
lean_object* v_h__16_1209_ = _args[16];
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(v_x_1193_, v_h__1_1194_, v_h__2_1195_, v_h__3_1196_, v_h__4_1197_, v_h__5_1198_, v_h__6_1199_, v_h__7_1200_, v_h__8_1201_, v_h__9_1202_, v_h__10_1203_, v_h__11_1204_, v_h__12_1205_, v_h__13_1206_, v_h__14_1207_, v_h__15_1208_, v_h__16_1209_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(lean_object* v_motive_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_, lean_object* v_h__1_1214_, lean_object* v_h__2_1215_, lean_object* v_h__3_1216_, lean_object* v_h__4_1217_, lean_object* v_h__5_1218_, lean_object* v_h__6_1219_, lean_object* v_h__7_1220_, lean_object* v_h__8_1221_, lean_object* v_h__9_1222_, lean_object* v_h__10_1223_, lean_object* v_h__11_1224_, lean_object* v_h__12_1225_, lean_object* v_h__13_1226_, lean_object* v_h__14_1227_, lean_object* v_h__15_1228_, lean_object* v_h__16_1229_){
_start:
{
switch(lean_obj_tag(v_x_1213_))
{
case 0:
{
lean_object* v___x_1230_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
v___x_1230_ = lean_apply_1(v_h__1_1214_, lean_box(0));
return v___x_1230_;
}
case 1:
{
lean_object* v_f_1231_; lean_object* v___x_1232_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__1_1214_);
v_f_1231_ = lean_ctor_get(v_x_1213_, 0);
lean_inc_ref(v_f_1231_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1232_ = lean_apply_2(v_h__2_1215_, lean_box(0), v_f_1231_);
return v___x_1232_;
}
case 2:
{
lean_object* v_s_1233_; lean_object* v___x_1234_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_s_1233_ = lean_ctor_get(v_x_1213_, 0);
lean_inc_ref(v_s_1233_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1234_ = lean_apply_2(v_h__3_1216_, lean_box(0), v_s_1233_);
return v___x_1234_;
}
case 3:
{
lean_object* v_id_1235_; lean_object* v_d_1236_; lean_object* v___x_1237_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_id_1235_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_id_1235_);
v_d_1236_ = lean_ctor_get(v_x_1213_, 1);
lean_inc(v_d_1236_);
lean_dec_ref_known(v_x_1213_, 2);
v___x_1237_ = lean_apply_3(v_h__5_1218_, lean_box(0), v_id_1235_, v_d_1236_);
return v___x_1237_;
}
case 4:
{
lean_object* v_d_1238_; lean_object* v___x_1239_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_d_1238_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_d_1238_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1239_ = lean_apply_2(v_h__4_1217_, lean_box(0), v_d_1238_);
return v___x_1239_;
}
case 5:
{
lean_object* v_d_1240_; lean_object* v___x_1241_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_d_1240_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_d_1240_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1241_ = lean_apply_2(v_h__12_1225_, lean_box(0), v_d_1240_);
return v___x_1241_;
}
case 6:
{
lean_object* v_n_1242_; uint8_t v_isCumulative_1243_; lean_object* v_d_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_n_1242_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_n_1242_);
v_isCumulative_1243_ = lean_ctor_get_uint8(v_x_1213_, sizeof(void*)*2);
v_d_1244_ = lean_ctor_get(v_x_1213_, 1);
lean_inc(v_d_1244_);
lean_dec_ref_known(v_x_1213_, 2);
v___x_1245_ = lean_box(v_isCumulative_1243_);
v___x_1246_ = lean_apply_4(v_h__6_1219_, lean_box(0), v_n_1242_, v___x_1245_, v_d_1244_);
return v___x_1246_;
}
case 7:
{
lean_object* v_d_1247_; lean_object* v___x_1248_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_d_1247_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_d_1247_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1248_ = lean_apply_2(v_h__7_1220_, lean_box(0), v_d_1247_);
return v___x_1248_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1249_; lean_object* v_d_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_onlyNonCumulative_1249_ = lean_ctor_get_uint8(v_x_1213_, sizeof(void*)*1);
v_d_1250_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_d_1250_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1251_ = lean_box(v_onlyNonCumulative_1249_);
v___x_1252_ = lean_apply_3(v_h__8_1221_, lean_box(0), v___x_1251_, v_d_1250_);
return v___x_1252_;
}
case 9:
{
lean_object* v_d_1253_; lean_object* v___x_1254_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_d_1253_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_d_1253_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1254_ = lean_apply_2(v_h__9_1222_, lean_box(0), v_d_1253_);
return v___x_1254_;
}
case 10:
{
lean_object* v_d_1255_; lean_object* v___x_1256_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_d_1255_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_d_1255_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1256_ = lean_apply_2(v_h__10_1223_, lean_box(0), v_d_1255_);
return v___x_1256_;
}
case 11:
{
lean_object* v_d_1257_; lean_object* v___x_1258_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_d_1257_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_d_1257_);
lean_dec_ref_known(v_x_1213_, 1);
v___x_1258_ = lean_apply_2(v_h__11_1224_, lean_box(0), v_d_1257_);
return v___x_1258_;
}
case 12:
{
lean_object* v_p_1259_; lean_object* v_d_1260_; lean_object* v___x_1261_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_p_1259_ = lean_ctor_get(v_x_1213_, 0);
lean_inc_ref(v_p_1259_);
v_d_1260_ = lean_ctor_get(v_x_1213_, 1);
lean_inc(v_d_1260_);
lean_dec_ref_known(v_x_1213_, 2);
v___x_1261_ = lean_apply_3(v_h__13_1226_, lean_box(0), v_p_1259_, v_d_1260_);
return v___x_1261_;
}
case 13:
{
lean_object* v_cost_1262_; lean_object* v_d_1263_; lean_object* v___x_1264_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__15_1228_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_cost_1262_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_cost_1262_);
v_d_1263_ = lean_ctor_get(v_x_1213_, 1);
lean_inc(v_d_1263_);
lean_dec_ref_known(v_x_1213_, 2);
v___x_1264_ = lean_apply_3(v_h__14_1227_, lean_box(0), v_cost_1262_, v_d_1263_);
return v___x_1264_;
}
case 14:
{
lean_object* v_a_1265_; lean_object* v_b_1266_; lean_object* v___x_1267_; 
lean_dec(v_h__16_1229_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_a_1265_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_a_1265_);
v_b_1266_ = lean_ctor_get(v_x_1213_, 1);
lean_inc(v_b_1266_);
lean_dec_ref_known(v_x_1213_, 2);
v___x_1267_ = lean_apply_3(v_h__15_1228_, lean_box(0), v_a_1265_, v_b_1266_);
return v___x_1267_;
}
default: 
{
lean_object* v_a_1268_; lean_object* v_b_1269_; lean_object* v___x_1270_; 
lean_dec(v_h__15_1228_);
lean_dec(v_h__14_1227_);
lean_dec(v_h__13_1226_);
lean_dec(v_h__12_1225_);
lean_dec(v_h__11_1224_);
lean_dec(v_h__10_1223_);
lean_dec(v_h__9_1222_);
lean_dec(v_h__8_1221_);
lean_dec(v_h__7_1220_);
lean_dec(v_h__6_1219_);
lean_dec(v_h__5_1218_);
lean_dec(v_h__4_1217_);
lean_dec(v_h__3_1216_);
lean_dec(v_h__2_1215_);
lean_dec(v_h__1_1214_);
v_a_1268_ = lean_ctor_get(v_x_1213_, 0);
lean_inc(v_a_1268_);
v_b_1269_ = lean_ctor_get(v_x_1213_, 1);
lean_inc(v_b_1269_);
lean_dec_ref_known(v_x_1213_, 2);
v___x_1270_ = lean_apply_3(v_h__16_1229_, lean_box(0), v_a_1268_, v_b_1269_);
return v___x_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___boxed(lean_object** _args){
lean_object* v_motive_1271_ = _args[0];
lean_object* v_x_1272_ = _args[1];
lean_object* v_x_1273_ = _args[2];
lean_object* v_h__1_1274_ = _args[3];
lean_object* v_h__2_1275_ = _args[4];
lean_object* v_h__3_1276_ = _args[5];
lean_object* v_h__4_1277_ = _args[6];
lean_object* v_h__5_1278_ = _args[7];
lean_object* v_h__6_1279_ = _args[8];
lean_object* v_h__7_1280_ = _args[9];
lean_object* v_h__8_1281_ = _args[10];
lean_object* v_h__9_1282_ = _args[11];
lean_object* v_h__10_1283_ = _args[12];
lean_object* v_h__11_1284_ = _args[13];
lean_object* v_h__12_1285_ = _args[14];
lean_object* v_h__13_1286_ = _args[15];
lean_object* v_h__14_1287_ = _args[16];
lean_object* v_h__15_1288_ = _args[17];
lean_object* v_h__16_1289_ = _args[18];
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(v_motive_1271_, v_x_1272_, v_x_1273_, v_h__1_1274_, v_h__2_1275_, v_h__3_1276_, v_h__4_1277_, v_h__5_1278_, v_h__6_1279_, v_h__7_1280_, v_h__8_1281_, v_h__9_1282_, v_h__10_1283_, v_h__11_1284_, v_h__12_1285_, v_h__13_1286_, v_h__14_1287_, v_h__15_1288_, v_h__16_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(lean_object* v_x_1291_, lean_object* v_h__1_1292_, lean_object* v_h__2_1293_, lean_object* v_h__3_1294_, lean_object* v_h__4_1295_, lean_object* v_h__5_1296_, lean_object* v_h__6_1297_, lean_object* v_h__7_1298_, lean_object* v_h__8_1299_, lean_object* v_h__9_1300_, lean_object* v_h__10_1301_, lean_object* v_h__11_1302_, lean_object* v_h__12_1303_, lean_object* v_h__13_1304_, lean_object* v_h__14_1305_, lean_object* v_h__15_1306_, lean_object* v_h__16_1307_){
_start:
{
switch(lean_obj_tag(v_x_1291_))
{
case 0:
{
lean_object* v___x_1308_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
v___x_1308_ = lean_apply_1(v_h__1_1292_, lean_box(0));
return v___x_1308_;
}
case 1:
{
lean_object* v_f_1309_; lean_object* v___x_1310_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__1_1292_);
v_f_1309_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_f_1309_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1310_ = lean_apply_2(v_h__2_1293_, lean_box(0), v_f_1309_);
return v___x_1310_;
}
case 2:
{
lean_object* v_s_1311_; lean_object* v___x_1312_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_s_1311_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_s_1311_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1312_ = lean_apply_2(v_h__3_1294_, lean_box(0), v_s_1311_);
return v___x_1312_;
}
case 3:
{
lean_object* v_id_1313_; lean_object* v_d_1314_; lean_object* v___x_1315_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_id_1313_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_id_1313_);
v_d_1314_ = lean_ctor_get(v_x_1291_, 1);
lean_inc(v_d_1314_);
lean_dec_ref_known(v_x_1291_, 2);
v___x_1315_ = lean_apply_3(v_h__6_1297_, lean_box(0), v_id_1313_, v_d_1314_);
return v___x_1315_;
}
case 4:
{
lean_object* v_d_1316_; lean_object* v___x_1317_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_d_1316_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_d_1316_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1317_ = lean_apply_2(v_h__4_1295_, lean_box(0), v_d_1316_);
return v___x_1317_;
}
case 5:
{
lean_object* v_d_1318_; lean_object* v___x_1319_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_d_1318_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_d_1318_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1319_ = lean_apply_2(v_h__5_1296_, lean_box(0), v_d_1318_);
return v___x_1319_;
}
case 6:
{
lean_object* v_n_1320_; uint8_t v_isCumulative_1321_; lean_object* v_d_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_n_1320_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_n_1320_);
v_isCumulative_1321_ = lean_ctor_get_uint8(v_x_1291_, sizeof(void*)*2);
v_d_1322_ = lean_ctor_get(v_x_1291_, 1);
lean_inc(v_d_1322_);
lean_dec_ref_known(v_x_1291_, 2);
v___x_1323_ = lean_box(v_isCumulative_1321_);
v___x_1324_ = lean_apply_4(v_h__7_1298_, lean_box(0), v_n_1320_, v___x_1323_, v_d_1322_);
return v___x_1324_;
}
case 7:
{
lean_object* v_d_1325_; lean_object* v___x_1326_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_d_1325_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_d_1325_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1326_ = lean_apply_2(v_h__8_1299_, lean_box(0), v_d_1325_);
return v___x_1326_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1327_; lean_object* v_d_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_onlyNonCumulative_1327_ = lean_ctor_get_uint8(v_x_1291_, sizeof(void*)*1);
v_d_1328_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_d_1328_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1329_ = lean_box(v_onlyNonCumulative_1327_);
v___x_1330_ = lean_apply_3(v_h__9_1300_, lean_box(0), v___x_1329_, v_d_1328_);
return v___x_1330_;
}
case 9:
{
lean_object* v_d_1331_; lean_object* v___x_1332_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_d_1331_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_d_1331_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1332_ = lean_apply_2(v_h__10_1301_, lean_box(0), v_d_1331_);
return v___x_1332_;
}
case 10:
{
lean_object* v_d_1333_; lean_object* v___x_1334_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_d_1333_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_d_1333_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1334_ = lean_apply_2(v_h__11_1302_, lean_box(0), v_d_1333_);
return v___x_1334_;
}
case 11:
{
lean_object* v_d_1335_; lean_object* v___x_1336_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_d_1335_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_d_1335_);
lean_dec_ref_known(v_x_1291_, 1);
v___x_1336_ = lean_apply_2(v_h__12_1303_, lean_box(0), v_d_1335_);
return v___x_1336_;
}
case 12:
{
lean_object* v_p_1337_; lean_object* v_d_1338_; lean_object* v___x_1339_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_p_1337_ = lean_ctor_get(v_x_1291_, 0);
lean_inc_ref(v_p_1337_);
v_d_1338_ = lean_ctor_get(v_x_1291_, 1);
lean_inc(v_d_1338_);
lean_dec_ref_known(v_x_1291_, 2);
v___x_1339_ = lean_apply_3(v_h__13_1304_, lean_box(0), v_p_1337_, v_d_1338_);
return v___x_1339_;
}
case 13:
{
lean_object* v_cost_1340_; lean_object* v_d_1341_; lean_object* v___x_1342_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__15_1306_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_cost_1340_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_cost_1340_);
v_d_1341_ = lean_ctor_get(v_x_1291_, 1);
lean_inc(v_d_1341_);
lean_dec_ref_known(v_x_1291_, 2);
v___x_1342_ = lean_apply_3(v_h__14_1305_, lean_box(0), v_cost_1340_, v_d_1341_);
return v___x_1342_;
}
case 14:
{
lean_object* v_a_1343_; lean_object* v_b_1344_; lean_object* v___x_1345_; 
lean_dec(v_h__16_1307_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_a_1343_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_a_1343_);
v_b_1344_ = lean_ctor_get(v_x_1291_, 1);
lean_inc(v_b_1344_);
lean_dec_ref_known(v_x_1291_, 2);
v___x_1345_ = lean_apply_3(v_h__15_1306_, lean_box(0), v_a_1343_, v_b_1344_);
return v___x_1345_;
}
default: 
{
lean_object* v_a_1346_; lean_object* v_b_1347_; lean_object* v___x_1348_; 
lean_dec(v_h__15_1306_);
lean_dec(v_h__14_1305_);
lean_dec(v_h__13_1304_);
lean_dec(v_h__12_1303_);
lean_dec(v_h__11_1302_);
lean_dec(v_h__10_1301_);
lean_dec(v_h__9_1300_);
lean_dec(v_h__8_1299_);
lean_dec(v_h__7_1298_);
lean_dec(v_h__6_1297_);
lean_dec(v_h__5_1296_);
lean_dec(v_h__4_1295_);
lean_dec(v_h__3_1294_);
lean_dec(v_h__2_1293_);
lean_dec(v_h__1_1292_);
v_a_1346_ = lean_ctor_get(v_x_1291_, 0);
lean_inc(v_a_1346_);
v_b_1347_ = lean_ctor_get(v_x_1291_, 1);
lean_inc(v_b_1347_);
lean_dec_ref_known(v_x_1291_, 2);
v___x_1348_ = lean_apply_3(v_h__16_1307_, lean_box(0), v_a_1346_, v_b_1347_);
return v___x_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1349_ = _args[0];
lean_object* v_h__1_1350_ = _args[1];
lean_object* v_h__2_1351_ = _args[2];
lean_object* v_h__3_1352_ = _args[3];
lean_object* v_h__4_1353_ = _args[4];
lean_object* v_h__5_1354_ = _args[5];
lean_object* v_h__6_1355_ = _args[6];
lean_object* v_h__7_1356_ = _args[7];
lean_object* v_h__8_1357_ = _args[8];
lean_object* v_h__9_1358_ = _args[9];
lean_object* v_h__10_1359_ = _args[10];
lean_object* v_h__11_1360_ = _args[11];
lean_object* v_h__12_1361_ = _args[12];
lean_object* v_h__13_1362_ = _args[13];
lean_object* v_h__14_1363_ = _args[14];
lean_object* v_h__15_1364_ = _args[15];
lean_object* v_h__16_1365_ = _args[16];
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(v_x_1349_, v_h__1_1350_, v_h__2_1351_, v_h__3_1352_, v_h__4_1353_, v_h__5_1354_, v_h__6_1355_, v_h__7_1356_, v_h__8_1357_, v_h__9_1358_, v_h__10_1359_, v_h__11_1360_, v_h__12_1361_, v_h__13_1362_, v_h__14_1363_, v_h__15_1364_, v_h__16_1365_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(lean_object* v_motive_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_h__1_1370_, lean_object* v_h__2_1371_, lean_object* v_h__3_1372_, lean_object* v_h__4_1373_, lean_object* v_h__5_1374_, lean_object* v_h__6_1375_, lean_object* v_h__7_1376_, lean_object* v_h__8_1377_, lean_object* v_h__9_1378_, lean_object* v_h__10_1379_, lean_object* v_h__11_1380_, lean_object* v_h__12_1381_, lean_object* v_h__13_1382_, lean_object* v_h__14_1383_, lean_object* v_h__15_1384_, lean_object* v_h__16_1385_){
_start:
{
switch(lean_obj_tag(v_x_1369_))
{
case 0:
{
lean_object* v___x_1386_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
v___x_1386_ = lean_apply_1(v_h__1_1370_, lean_box(0));
return v___x_1386_;
}
case 1:
{
lean_object* v_f_1387_; lean_object* v___x_1388_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__1_1370_);
v_f_1387_ = lean_ctor_get(v_x_1369_, 0);
lean_inc_ref(v_f_1387_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1388_ = lean_apply_2(v_h__2_1371_, lean_box(0), v_f_1387_);
return v___x_1388_;
}
case 2:
{
lean_object* v_s_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_s_1389_ = lean_ctor_get(v_x_1369_, 0);
lean_inc_ref(v_s_1389_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1390_ = lean_apply_2(v_h__3_1372_, lean_box(0), v_s_1389_);
return v___x_1390_;
}
case 3:
{
lean_object* v_id_1391_; lean_object* v_d_1392_; lean_object* v___x_1393_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_id_1391_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_id_1391_);
v_d_1392_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_d_1392_);
lean_dec_ref_known(v_x_1369_, 2);
v___x_1393_ = lean_apply_3(v_h__6_1375_, lean_box(0), v_id_1391_, v_d_1392_);
return v___x_1393_;
}
case 4:
{
lean_object* v_d_1394_; lean_object* v___x_1395_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_d_1394_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_d_1394_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1395_ = lean_apply_2(v_h__4_1373_, lean_box(0), v_d_1394_);
return v___x_1395_;
}
case 5:
{
lean_object* v_d_1396_; lean_object* v___x_1397_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_d_1396_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_d_1396_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1397_ = lean_apply_2(v_h__5_1374_, lean_box(0), v_d_1396_);
return v___x_1397_;
}
case 6:
{
lean_object* v_n_1398_; uint8_t v_isCumulative_1399_; lean_object* v_d_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_n_1398_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_n_1398_);
v_isCumulative_1399_ = lean_ctor_get_uint8(v_x_1369_, sizeof(void*)*2);
v_d_1400_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_d_1400_);
lean_dec_ref_known(v_x_1369_, 2);
v___x_1401_ = lean_box(v_isCumulative_1399_);
v___x_1402_ = lean_apply_4(v_h__7_1376_, lean_box(0), v_n_1398_, v___x_1401_, v_d_1400_);
return v___x_1402_;
}
case 7:
{
lean_object* v_d_1403_; lean_object* v___x_1404_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_d_1403_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_d_1403_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1404_ = lean_apply_2(v_h__8_1377_, lean_box(0), v_d_1403_);
return v___x_1404_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1405_; lean_object* v_d_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_onlyNonCumulative_1405_ = lean_ctor_get_uint8(v_x_1369_, sizeof(void*)*1);
v_d_1406_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_d_1406_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1407_ = lean_box(v_onlyNonCumulative_1405_);
v___x_1408_ = lean_apply_3(v_h__9_1378_, lean_box(0), v___x_1407_, v_d_1406_);
return v___x_1408_;
}
case 9:
{
lean_object* v_d_1409_; lean_object* v___x_1410_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_d_1409_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_d_1409_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1410_ = lean_apply_2(v_h__10_1379_, lean_box(0), v_d_1409_);
return v___x_1410_;
}
case 10:
{
lean_object* v_d_1411_; lean_object* v___x_1412_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_d_1411_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_d_1411_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1412_ = lean_apply_2(v_h__11_1380_, lean_box(0), v_d_1411_);
return v___x_1412_;
}
case 11:
{
lean_object* v_d_1413_; lean_object* v___x_1414_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_d_1413_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_d_1413_);
lean_dec_ref_known(v_x_1369_, 1);
v___x_1414_ = lean_apply_2(v_h__12_1381_, lean_box(0), v_d_1413_);
return v___x_1414_;
}
case 12:
{
lean_object* v_p_1415_; lean_object* v_d_1416_; lean_object* v___x_1417_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_p_1415_ = lean_ctor_get(v_x_1369_, 0);
lean_inc_ref(v_p_1415_);
v_d_1416_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_d_1416_);
lean_dec_ref_known(v_x_1369_, 2);
v___x_1417_ = lean_apply_3(v_h__13_1382_, lean_box(0), v_p_1415_, v_d_1416_);
return v___x_1417_;
}
case 13:
{
lean_object* v_cost_1418_; lean_object* v_d_1419_; lean_object* v___x_1420_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__15_1384_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_cost_1418_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_cost_1418_);
v_d_1419_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_d_1419_);
lean_dec_ref_known(v_x_1369_, 2);
v___x_1420_ = lean_apply_3(v_h__14_1383_, lean_box(0), v_cost_1418_, v_d_1419_);
return v___x_1420_;
}
case 14:
{
lean_object* v_a_1421_; lean_object* v_b_1422_; lean_object* v___x_1423_; 
lean_dec(v_h__16_1385_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_a_1421_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_a_1421_);
v_b_1422_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_b_1422_);
lean_dec_ref_known(v_x_1369_, 2);
v___x_1423_ = lean_apply_3(v_h__15_1384_, lean_box(0), v_a_1421_, v_b_1422_);
return v___x_1423_;
}
default: 
{
lean_object* v_a_1424_; lean_object* v_b_1425_; lean_object* v___x_1426_; 
lean_dec(v_h__15_1384_);
lean_dec(v_h__14_1383_);
lean_dec(v_h__13_1382_);
lean_dec(v_h__12_1381_);
lean_dec(v_h__11_1380_);
lean_dec(v_h__10_1379_);
lean_dec(v_h__9_1378_);
lean_dec(v_h__8_1377_);
lean_dec(v_h__7_1376_);
lean_dec(v_h__6_1375_);
lean_dec(v_h__5_1374_);
lean_dec(v_h__4_1373_);
lean_dec(v_h__3_1372_);
lean_dec(v_h__2_1371_);
lean_dec(v_h__1_1370_);
v_a_1424_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_a_1424_);
v_b_1425_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_b_1425_);
lean_dec_ref_known(v_x_1369_, 2);
v___x_1426_ = lean_apply_3(v_h__16_1385_, lean_box(0), v_a_1424_, v_b_1425_);
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___boxed(lean_object** _args){
lean_object* v_motive_1427_ = _args[0];
lean_object* v_x_1428_ = _args[1];
lean_object* v_x_1429_ = _args[2];
lean_object* v_h__1_1430_ = _args[3];
lean_object* v_h__2_1431_ = _args[4];
lean_object* v_h__3_1432_ = _args[5];
lean_object* v_h__4_1433_ = _args[6];
lean_object* v_h__5_1434_ = _args[7];
lean_object* v_h__6_1435_ = _args[8];
lean_object* v_h__7_1436_ = _args[9];
lean_object* v_h__8_1437_ = _args[10];
lean_object* v_h__9_1438_ = _args[11];
lean_object* v_h__10_1439_ = _args[12];
lean_object* v_h__11_1440_ = _args[13];
lean_object* v_h__12_1441_ = _args[14];
lean_object* v_h__13_1442_ = _args[15];
lean_object* v_h__14_1443_ = _args[16];
lean_object* v_h__15_1444_ = _args[17];
lean_object* v_h__16_1445_ = _args[18];
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(v_motive_1427_, v_x_1428_, v_x_1429_, v_h__1_1430_, v_h__2_1431_, v_h__3_1432_, v_h__4_1433_, v_h__5_1434_, v_h__6_1435_, v_h__7_1436_, v_h__8_1437_, v_h__9_1438_, v_h__10_1439_, v_h__11_1440_, v_h__12_1441_, v_h__13_1442_, v_h__14_1443_, v_h__15_1444_, v_h__16_1445_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t v_x_1447_, lean_object* v_h__1_1448_, lean_object* v_h__2_1449_, lean_object* v_h__3_1450_){
_start:
{
switch(v_x_1447_)
{
case 0:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v_h__3_1450_);
lean_dec(v_h__2_1449_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_apply_1(v_h__1_1448_, v___x_1451_);
return v___x_1452_;
}
case 1:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_dec(v_h__3_1450_);
lean_dec(v_h__1_1448_);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_apply_1(v_h__2_1449_, v___x_1453_);
return v___x_1454_;
}
default: 
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec(v_h__2_1449_);
lean_dec(v_h__1_1448_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_apply_1(v_h__3_1450_, v___x_1455_);
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object* v_x_1457_, lean_object* v_h__1_1458_, lean_object* v_h__2_1459_, lean_object* v_h__3_1460_){
_start:
{
uint8_t v_x_33__boxed_1461_; lean_object* v_res_1462_; 
v_x_33__boxed_1461_ = lean_unbox(v_x_1457_);
v_res_1462_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(v_x_33__boxed_1461_, v_h__1_1458_, v_h__2_1459_, v_h__3_1460_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object* v_motive_1463_, uint8_t v_x_1464_, lean_object* v_h__1_1465_, lean_object* v_h__2_1466_, lean_object* v_h__3_1467_){
_start:
{
switch(v_x_1464_)
{
case 0:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v_h__3_1467_);
lean_dec(v_h__2_1466_);
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_apply_1(v_h__1_1465_, v___x_1468_);
return v___x_1469_;
}
case 1:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
lean_dec(v_h__3_1467_);
lean_dec(v_h__1_1465_);
v___x_1470_ = lean_box(0);
v___x_1471_ = lean_apply_1(v_h__2_1466_, v___x_1470_);
return v___x_1471_;
}
default: 
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_h__2_1466_);
lean_dec(v_h__1_1465_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_apply_1(v_h__3_1467_, v___x_1472_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object* v_motive_1474_, lean_object* v_x_1475_, lean_object* v_h__1_1476_, lean_object* v_h__2_1477_, lean_object* v_h__3_1478_){
_start:
{
uint8_t v_x_48__boxed_1479_; lean_object* v_res_1480_; 
v_x_48__boxed_1479_ = lean_unbox(v_x_1475_);
v_res_1480_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(v_motive_1474_, v_x_48__boxed_1479_, v_h__1_1476_, v_h__2_1477_, v_h__3_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object* v_x_1481_, lean_object* v_h__1_1482_, lean_object* v_h__2_1483_, lean_object* v_h__3_1484_, lean_object* v_h__4_1485_, lean_object* v_h__5_1486_, lean_object* v_h__6_1487_, lean_object* v_h__7_1488_, lean_object* v_h__8_1489_, lean_object* v_h__9_1490_, lean_object* v_h__10_1491_, lean_object* v_h__11_1492_, lean_object* v_h__12_1493_, lean_object* v_h__13_1494_, lean_object* v_h__14_1495_, lean_object* v_h__15_1496_, lean_object* v_h__16_1497_){
_start:
{
switch(lean_obj_tag(v_x_1481_))
{
case 0:
{
lean_object* v___x_1498_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
v___x_1498_ = lean_apply_1(v_h__1_1482_, lean_box(0));
return v___x_1498_;
}
case 1:
{
lean_object* v_f_1499_; lean_object* v___x_1500_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_f_1499_ = lean_ctor_get(v_x_1481_, 0);
lean_inc_ref(v_f_1499_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1500_ = lean_apply_2(v_h__3_1484_, lean_box(0), v_f_1499_);
return v___x_1500_;
}
case 2:
{
lean_object* v_s_1501_; lean_object* v___x_1502_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__1_1482_);
v_s_1501_ = lean_ctor_get(v_x_1481_, 0);
lean_inc_ref(v_s_1501_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1502_ = lean_apply_2(v_h__2_1483_, lean_box(0), v_s_1501_);
return v___x_1502_;
}
case 3:
{
lean_object* v_id_1503_; lean_object* v_d_1504_; lean_object* v___x_1505_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_id_1503_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_id_1503_);
v_d_1504_ = lean_ctor_get(v_x_1481_, 1);
lean_inc(v_d_1504_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1505_ = lean_apply_3(v_h__6_1487_, lean_box(0), v_id_1503_, v_d_1504_);
return v___x_1505_;
}
case 4:
{
lean_object* v_d_1506_; lean_object* v___x_1507_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_d_1506_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_d_1506_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1507_ = lean_apply_2(v_h__4_1485_, lean_box(0), v_d_1506_);
return v___x_1507_;
}
case 5:
{
lean_object* v_d_1508_; lean_object* v___x_1509_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_d_1508_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_d_1508_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1509_ = lean_apply_2(v_h__5_1486_, lean_box(0), v_d_1508_);
return v___x_1509_;
}
case 6:
{
lean_object* v_n_1510_; uint8_t v_isCumulative_1511_; lean_object* v_d_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_n_1510_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_n_1510_);
v_isCumulative_1511_ = lean_ctor_get_uint8(v_x_1481_, sizeof(void*)*2);
v_d_1512_ = lean_ctor_get(v_x_1481_, 1);
lean_inc(v_d_1512_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1513_ = lean_box(v_isCumulative_1511_);
v___x_1514_ = lean_apply_4(v_h__7_1488_, lean_box(0), v_n_1510_, v___x_1513_, v_d_1512_);
return v___x_1514_;
}
case 7:
{
lean_object* v_d_1515_; lean_object* v___x_1516_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_d_1515_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_d_1515_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1516_ = lean_apply_2(v_h__8_1489_, lean_box(0), v_d_1515_);
return v___x_1516_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1517_; lean_object* v_d_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_onlyNonCumulative_1517_ = lean_ctor_get_uint8(v_x_1481_, sizeof(void*)*1);
v_d_1518_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_d_1518_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1519_ = lean_box(v_onlyNonCumulative_1517_);
v___x_1520_ = lean_apply_3(v_h__9_1490_, lean_box(0), v___x_1519_, v_d_1518_);
return v___x_1520_;
}
case 9:
{
lean_object* v_d_1521_; lean_object* v___x_1522_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_d_1521_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_d_1521_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1522_ = lean_apply_2(v_h__10_1491_, lean_box(0), v_d_1521_);
return v___x_1522_;
}
case 10:
{
lean_object* v_d_1523_; lean_object* v___x_1524_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_d_1523_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_d_1523_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1524_ = lean_apply_2(v_h__11_1492_, lean_box(0), v_d_1523_);
return v___x_1524_;
}
case 11:
{
lean_object* v_d_1525_; lean_object* v___x_1526_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_d_1525_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_d_1525_);
lean_dec_ref_known(v_x_1481_, 1);
v___x_1526_ = lean_apply_2(v_h__12_1493_, lean_box(0), v_d_1525_);
return v___x_1526_;
}
case 12:
{
lean_object* v_p_1527_; lean_object* v_d_1528_; lean_object* v___x_1529_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_p_1527_ = lean_ctor_get(v_x_1481_, 0);
lean_inc_ref(v_p_1527_);
v_d_1528_ = lean_ctor_get(v_x_1481_, 1);
lean_inc(v_d_1528_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1529_ = lean_apply_3(v_h__13_1494_, lean_box(0), v_p_1527_, v_d_1528_);
return v___x_1529_;
}
case 13:
{
lean_object* v_cost_1530_; lean_object* v_d_1531_; lean_object* v___x_1532_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__15_1496_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_cost_1530_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_cost_1530_);
v_d_1531_ = lean_ctor_get(v_x_1481_, 1);
lean_inc(v_d_1531_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1532_ = lean_apply_3(v_h__14_1495_, lean_box(0), v_cost_1530_, v_d_1531_);
return v___x_1532_;
}
case 14:
{
lean_object* v_a_1533_; lean_object* v_b_1534_; lean_object* v___x_1535_; 
lean_dec(v_h__16_1497_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_a_1533_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_a_1533_);
v_b_1534_ = lean_ctor_get(v_x_1481_, 1);
lean_inc(v_b_1534_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1535_ = lean_apply_3(v_h__15_1496_, lean_box(0), v_a_1533_, v_b_1534_);
return v___x_1535_;
}
default: 
{
lean_object* v_a_1536_; lean_object* v_b_1537_; lean_object* v___x_1538_; 
lean_dec(v_h__15_1496_);
lean_dec(v_h__14_1495_);
lean_dec(v_h__13_1494_);
lean_dec(v_h__12_1493_);
lean_dec(v_h__11_1492_);
lean_dec(v_h__10_1491_);
lean_dec(v_h__9_1490_);
lean_dec(v_h__8_1489_);
lean_dec(v_h__7_1488_);
lean_dec(v_h__6_1487_);
lean_dec(v_h__5_1486_);
lean_dec(v_h__4_1485_);
lean_dec(v_h__3_1484_);
lean_dec(v_h__2_1483_);
lean_dec(v_h__1_1482_);
v_a_1536_ = lean_ctor_get(v_x_1481_, 0);
lean_inc(v_a_1536_);
v_b_1537_ = lean_ctor_get(v_x_1481_, 1);
lean_inc(v_b_1537_);
lean_dec_ref_known(v_x_1481_, 2);
v___x_1538_ = lean_apply_3(v_h__16_1497_, lean_box(0), v_a_1536_, v_b_1537_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1539_ = _args[0];
lean_object* v_h__1_1540_ = _args[1];
lean_object* v_h__2_1541_ = _args[2];
lean_object* v_h__3_1542_ = _args[3];
lean_object* v_h__4_1543_ = _args[4];
lean_object* v_h__5_1544_ = _args[5];
lean_object* v_h__6_1545_ = _args[6];
lean_object* v_h__7_1546_ = _args[7];
lean_object* v_h__8_1547_ = _args[8];
lean_object* v_h__9_1548_ = _args[9];
lean_object* v_h__10_1549_ = _args[10];
lean_object* v_h__11_1550_ = _args[11];
lean_object* v_h__12_1551_ = _args[12];
lean_object* v_h__13_1552_ = _args[13];
lean_object* v_h__14_1553_ = _args[14];
lean_object* v_h__15_1554_ = _args[15];
lean_object* v_h__16_1555_ = _args[16];
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(v_x_1539_, v_h__1_1540_, v_h__2_1541_, v_h__3_1542_, v_h__4_1543_, v_h__5_1544_, v_h__6_1545_, v_h__7_1546_, v_h__8_1547_, v_h__9_1548_, v_h__10_1549_, v_h__11_1550_, v_h__12_1551_, v_h__13_1552_, v_h__14_1553_, v_h__15_1554_, v_h__16_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object* v_motive_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v_h__1_1560_, lean_object* v_h__2_1561_, lean_object* v_h__3_1562_, lean_object* v_h__4_1563_, lean_object* v_h__5_1564_, lean_object* v_h__6_1565_, lean_object* v_h__7_1566_, lean_object* v_h__8_1567_, lean_object* v_h__9_1568_, lean_object* v_h__10_1569_, lean_object* v_h__11_1570_, lean_object* v_h__12_1571_, lean_object* v_h__13_1572_, lean_object* v_h__14_1573_, lean_object* v_h__15_1574_, lean_object* v_h__16_1575_){
_start:
{
switch(lean_obj_tag(v_x_1559_))
{
case 0:
{
lean_object* v___x_1576_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
v___x_1576_ = lean_apply_1(v_h__1_1560_, lean_box(0));
return v___x_1576_;
}
case 1:
{
lean_object* v_f_1577_; lean_object* v___x_1578_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_f_1577_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_f_1577_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1578_ = lean_apply_2(v_h__3_1562_, lean_box(0), v_f_1577_);
return v___x_1578_;
}
case 2:
{
lean_object* v_s_1579_; lean_object* v___x_1580_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__1_1560_);
v_s_1579_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_s_1579_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1580_ = lean_apply_2(v_h__2_1561_, lean_box(0), v_s_1579_);
return v___x_1580_;
}
case 3:
{
lean_object* v_id_1581_; lean_object* v_d_1582_; lean_object* v___x_1583_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_id_1581_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_id_1581_);
v_d_1582_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_d_1582_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1583_ = lean_apply_3(v_h__6_1565_, lean_box(0), v_id_1581_, v_d_1582_);
return v___x_1583_;
}
case 4:
{
lean_object* v_d_1584_; lean_object* v___x_1585_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_d_1584_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_d_1584_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1585_ = lean_apply_2(v_h__4_1563_, lean_box(0), v_d_1584_);
return v___x_1585_;
}
case 5:
{
lean_object* v_d_1586_; lean_object* v___x_1587_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_d_1586_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_d_1586_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1587_ = lean_apply_2(v_h__5_1564_, lean_box(0), v_d_1586_);
return v___x_1587_;
}
case 6:
{
lean_object* v_n_1588_; uint8_t v_isCumulative_1589_; lean_object* v_d_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_n_1588_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_n_1588_);
v_isCumulative_1589_ = lean_ctor_get_uint8(v_x_1559_, sizeof(void*)*2);
v_d_1590_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_d_1590_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1591_ = lean_box(v_isCumulative_1589_);
v___x_1592_ = lean_apply_4(v_h__7_1566_, lean_box(0), v_n_1588_, v___x_1591_, v_d_1590_);
return v___x_1592_;
}
case 7:
{
lean_object* v_d_1593_; lean_object* v___x_1594_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_d_1593_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_d_1593_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1594_ = lean_apply_2(v_h__8_1567_, lean_box(0), v_d_1593_);
return v___x_1594_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1595_; lean_object* v_d_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_onlyNonCumulative_1595_ = lean_ctor_get_uint8(v_x_1559_, sizeof(void*)*1);
v_d_1596_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_d_1596_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1597_ = lean_box(v_onlyNonCumulative_1595_);
v___x_1598_ = lean_apply_3(v_h__9_1568_, lean_box(0), v___x_1597_, v_d_1596_);
return v___x_1598_;
}
case 9:
{
lean_object* v_d_1599_; lean_object* v___x_1600_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_d_1599_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_d_1599_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1600_ = lean_apply_2(v_h__10_1569_, lean_box(0), v_d_1599_);
return v___x_1600_;
}
case 10:
{
lean_object* v_d_1601_; lean_object* v___x_1602_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_d_1601_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_d_1601_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1602_ = lean_apply_2(v_h__11_1570_, lean_box(0), v_d_1601_);
return v___x_1602_;
}
case 11:
{
lean_object* v_d_1603_; lean_object* v___x_1604_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_d_1603_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_d_1603_);
lean_dec_ref_known(v_x_1559_, 1);
v___x_1604_ = lean_apply_2(v_h__12_1571_, lean_box(0), v_d_1603_);
return v___x_1604_;
}
case 12:
{
lean_object* v_p_1605_; lean_object* v_d_1606_; lean_object* v___x_1607_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_p_1605_ = lean_ctor_get(v_x_1559_, 0);
lean_inc_ref(v_p_1605_);
v_d_1606_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_d_1606_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1607_ = lean_apply_3(v_h__13_1572_, lean_box(0), v_p_1605_, v_d_1606_);
return v___x_1607_;
}
case 13:
{
lean_object* v_cost_1608_; lean_object* v_d_1609_; lean_object* v___x_1610_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__15_1574_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_cost_1608_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_cost_1608_);
v_d_1609_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_d_1609_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1610_ = lean_apply_3(v_h__14_1573_, lean_box(0), v_cost_1608_, v_d_1609_);
return v___x_1610_;
}
case 14:
{
lean_object* v_a_1611_; lean_object* v_b_1612_; lean_object* v___x_1613_; 
lean_dec(v_h__16_1575_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_a_1611_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_a_1611_);
v_b_1612_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_b_1612_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1613_ = lean_apply_3(v_h__15_1574_, lean_box(0), v_a_1611_, v_b_1612_);
return v___x_1613_;
}
default: 
{
lean_object* v_a_1614_; lean_object* v_b_1615_; lean_object* v___x_1616_; 
lean_dec(v_h__15_1574_);
lean_dec(v_h__14_1573_);
lean_dec(v_h__13_1572_);
lean_dec(v_h__12_1571_);
lean_dec(v_h__11_1570_);
lean_dec(v_h__10_1569_);
lean_dec(v_h__9_1568_);
lean_dec(v_h__8_1567_);
lean_dec(v_h__7_1566_);
lean_dec(v_h__6_1565_);
lean_dec(v_h__5_1564_);
lean_dec(v_h__4_1563_);
lean_dec(v_h__3_1562_);
lean_dec(v_h__2_1561_);
lean_dec(v_h__1_1560_);
v_a_1614_ = lean_ctor_get(v_x_1559_, 0);
lean_inc(v_a_1614_);
v_b_1615_ = lean_ctor_get(v_x_1559_, 1);
lean_inc(v_b_1615_);
lean_dec_ref_known(v_x_1559_, 2);
v___x_1616_ = lean_apply_3(v_h__16_1575_, lean_box(0), v_a_1614_, v_b_1615_);
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object** _args){
lean_object* v_motive_1617_ = _args[0];
lean_object* v_x_1618_ = _args[1];
lean_object* v_x_1619_ = _args[2];
lean_object* v_h__1_1620_ = _args[3];
lean_object* v_h__2_1621_ = _args[4];
lean_object* v_h__3_1622_ = _args[5];
lean_object* v_h__4_1623_ = _args[6];
lean_object* v_h__5_1624_ = _args[7];
lean_object* v_h__6_1625_ = _args[8];
lean_object* v_h__7_1626_ = _args[9];
lean_object* v_h__8_1627_ = _args[10];
lean_object* v_h__9_1628_ = _args[11];
lean_object* v_h__10_1629_ = _args[12];
lean_object* v_h__11_1630_ = _args[13];
lean_object* v_h__12_1631_ = _args[14];
lean_object* v_h__13_1632_ = _args[15];
lean_object* v_h__14_1633_ = _args[16];
lean_object* v_h__15_1634_ = _args[17];
lean_object* v_h__16_1635_ = _args[18];
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(v_motive_1617_, v_x_1618_, v_x_1619_, v_h__1_1620_, v_h__2_1621_, v_h__3_1622_, v_h__4_1623_, v_h__5_1624_, v_h__6_1625_, v_h__7_1626_, v_h__8_1627_, v_h__9_1628_, v_h__10_1629_, v_h__11_1630_, v_h__12_1631_, v_h__13_1632_, v_h__14_1633_, v_h__15_1634_, v_h__16_1635_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t v_x_1637_, lean_object* v_h__1_1638_, lean_object* v_h__2_1639_, lean_object* v_h__3_1640_, lean_object* v_h__4_1641_, lean_object* v_h__5_1642_){
_start:
{
switch(v_x_1637_)
{
case 0:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_h__5_1642_);
lean_dec(v_h__4_1641_);
lean_dec(v_h__3_1640_);
lean_dec(v_h__2_1639_);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_apply_1(v_h__1_1638_, v___x_1643_);
return v___x_1644_;
}
case 1:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec(v_h__5_1642_);
lean_dec(v_h__4_1641_);
lean_dec(v_h__3_1640_);
lean_dec(v_h__1_1638_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_apply_1(v_h__2_1639_, v___x_1645_);
return v___x_1646_;
}
case 2:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec(v_h__5_1642_);
lean_dec(v_h__4_1641_);
lean_dec(v_h__2_1639_);
lean_dec(v_h__1_1638_);
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_apply_1(v_h__3_1640_, v___x_1647_);
return v___x_1648_;
}
case 3:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec(v_h__5_1642_);
lean_dec(v_h__3_1640_);
lean_dec(v_h__2_1639_);
lean_dec(v_h__1_1638_);
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_apply_1(v_h__4_1641_, v___x_1649_);
return v___x_1650_;
}
default: 
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v_h__4_1641_);
lean_dec(v_h__3_1640_);
lean_dec(v_h__2_1639_);
lean_dec(v_h__1_1638_);
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_apply_1(v_h__5_1642_, v___x_1651_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object* v_x_1653_, lean_object* v_h__1_1654_, lean_object* v_h__2_1655_, lean_object* v_h__3_1656_, lean_object* v_h__4_1657_, lean_object* v_h__5_1658_){
_start:
{
uint8_t v_x_51__boxed_1659_; lean_object* v_res_1660_; 
v_x_51__boxed_1659_ = lean_unbox(v_x_1653_);
v_res_1660_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(v_x_51__boxed_1659_, v_h__1_1654_, v_h__2_1655_, v_h__3_1656_, v_h__4_1657_, v_h__5_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object* v_motive_1661_, uint8_t v_x_1662_, lean_object* v_h__1_1663_, lean_object* v_h__2_1664_, lean_object* v_h__3_1665_, lean_object* v_h__4_1666_, lean_object* v_h__5_1667_){
_start:
{
switch(v_x_1662_)
{
case 0:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_h__5_1667_);
lean_dec(v_h__4_1666_);
lean_dec(v_h__3_1665_);
lean_dec(v_h__2_1664_);
v___x_1668_ = lean_box(0);
v___x_1669_ = lean_apply_1(v_h__1_1663_, v___x_1668_);
return v___x_1669_;
}
case 1:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec(v_h__5_1667_);
lean_dec(v_h__4_1666_);
lean_dec(v_h__3_1665_);
lean_dec(v_h__1_1663_);
v___x_1670_ = lean_box(0);
v___x_1671_ = lean_apply_1(v_h__2_1664_, v___x_1670_);
return v___x_1671_;
}
case 2:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
lean_dec(v_h__5_1667_);
lean_dec(v_h__4_1666_);
lean_dec(v_h__2_1664_);
lean_dec(v_h__1_1663_);
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_apply_1(v_h__3_1665_, v___x_1672_);
return v___x_1673_;
}
case 3:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v_h__5_1667_);
lean_dec(v_h__3_1665_);
lean_dec(v_h__2_1664_);
lean_dec(v_h__1_1663_);
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_apply_1(v_h__4_1666_, v___x_1674_);
return v___x_1675_;
}
default: 
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v_h__4_1666_);
lean_dec(v_h__3_1665_);
lean_dec(v_h__2_1664_);
lean_dec(v_h__1_1663_);
v___x_1676_ = lean_box(0);
v___x_1677_ = lean_apply_1(v_h__5_1667_, v___x_1676_);
return v___x_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object* v_motive_1678_, lean_object* v_x_1679_, lean_object* v_h__1_1680_, lean_object* v_h__2_1681_, lean_object* v_h__3_1682_, lean_object* v_h__4_1683_, lean_object* v_h__5_1684_){
_start:
{
uint8_t v_x_74__boxed_1685_; lean_object* v_res_1686_; 
v_x_74__boxed_1685_ = lean_unbox(v_x_1679_);
v_res_1686_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(v_motive_1678_, v_x_74__boxed_1685_, v_h__1_1680_, v_h__2_1681_, v_h__3_1682_, v_h__4_1683_, v_h__5_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg(lean_object* v_t_1687_, lean_object* v_failure_1688_, lean_object* v_newline_1689_, lean_object* v_text_1690_, lean_object* v_tagged_1691_, lean_object* v_flattened_1692_, lean_object* v_unflattenable_1693_, lean_object* v_indented_1694_, lean_object* v_aligned_1695_, lean_object* v_unindented_1696_, lean_object* v_final_1697_, lean_object* v_initial_1698_, lean_object* v_free_1699_, lean_object* v_guarded_1700_, lean_object* v_costing_1701_, lean_object* v_either_1702_, lean_object* v_append_1703_){
_start:
{
switch(lean_obj_tag(v_t_1687_))
{
case 0:
{
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
lean_inc(v_failure_1688_);
return v_failure_1688_;
}
case 1:
{
lean_object* v_f_1704_; lean_object* v___x_1705_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
v_f_1704_ = lean_ctor_get(v_t_1687_, 1);
lean_inc_ref(v_f_1704_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1705_ = lean_apply_1(v_newline_1689_, v_f_1704_);
return v___x_1705_;
}
case 2:
{
lean_object* v_s_1706_; lean_object* v___x_1707_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_newline_1689_);
v_s_1706_ = lean_ctor_get(v_t_1687_, 1);
lean_inc_ref(v_s_1706_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1707_ = lean_apply_1(v_text_1690_, v_s_1706_);
return v___x_1707_;
}
case 3:
{
lean_object* v_id_1708_; lean_object* v_d_1709_; lean_object* v___x_1710_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_id_1708_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_id_1708_);
v_d_1709_ = lean_ctor_get(v_t_1687_, 2);
lean_inc(v_d_1709_);
lean_dec_ref_known(v_t_1687_, 3);
v___x_1710_ = lean_apply_2(v_tagged_1691_, v_id_1708_, v_d_1709_);
return v___x_1710_;
}
case 4:
{
lean_object* v_d_1711_; lean_object* v___x_1712_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_d_1711_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_d_1711_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1712_ = lean_apply_1(v_flattened_1692_, v_d_1711_);
return v___x_1712_;
}
case 5:
{
lean_object* v_d_1713_; lean_object* v___x_1714_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_d_1713_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_d_1713_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1714_ = lean_apply_1(v_unflattenable_1693_, v_d_1713_);
return v___x_1714_;
}
case 6:
{
lean_object* v_n_1715_; uint8_t v_isCumulative_1716_; lean_object* v_d_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_n_1715_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_n_1715_);
v_isCumulative_1716_ = lean_ctor_get_uint8(v_t_1687_, sizeof(void*)*3 + 7);
v_d_1717_ = lean_ctor_get(v_t_1687_, 2);
lean_inc(v_d_1717_);
lean_dec_ref_known(v_t_1687_, 3);
v___x_1718_ = lean_box(v_isCumulative_1716_);
v___x_1719_ = lean_apply_3(v_indented_1694_, v_n_1715_, v___x_1718_, v_d_1717_);
return v___x_1719_;
}
case 7:
{
lean_object* v_d_1720_; lean_object* v___x_1721_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_d_1720_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_d_1720_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1721_ = lean_apply_1(v_aligned_1695_, v_d_1720_);
return v___x_1721_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1722_; lean_object* v_d_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_onlyNonCumulative_1722_ = lean_ctor_get_uint8(v_t_1687_, sizeof(void*)*2 + 7);
v_d_1723_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_d_1723_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1724_ = lean_box(v_onlyNonCumulative_1722_);
v___x_1725_ = lean_apply_2(v_unindented_1696_, v___x_1724_, v_d_1723_);
return v___x_1725_;
}
case 9:
{
lean_object* v_d_1726_; lean_object* v___x_1727_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_d_1726_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_d_1726_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1727_ = lean_apply_1(v_final_1697_, v_d_1726_);
return v___x_1727_;
}
case 10:
{
lean_object* v_d_1728_; lean_object* v___x_1729_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_d_1728_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_d_1728_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1729_ = lean_apply_1(v_initial_1698_, v_d_1728_);
return v___x_1729_;
}
case 11:
{
lean_object* v_d_1730_; lean_object* v___x_1731_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_d_1730_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_d_1730_);
lean_dec_ref_known(v_t_1687_, 2);
v___x_1731_ = lean_apply_1(v_free_1699_, v_d_1730_);
return v___x_1731_;
}
case 12:
{
lean_object* v_p_1732_; lean_object* v_d_1733_; lean_object* v___x_1734_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_p_1732_ = lean_ctor_get(v_t_1687_, 1);
lean_inc_ref(v_p_1732_);
v_d_1733_ = lean_ctor_get(v_t_1687_, 2);
lean_inc(v_d_1733_);
lean_dec_ref_known(v_t_1687_, 3);
v___x_1734_ = lean_apply_2(v_guarded_1700_, v_p_1732_, v_d_1733_);
return v___x_1734_;
}
case 13:
{
lean_object* v_cost_1735_; lean_object* v_d_1736_; lean_object* v___x_1737_; 
lean_dec(v_append_1703_);
lean_dec(v_either_1702_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_cost_1735_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_cost_1735_);
v_d_1736_ = lean_ctor_get(v_t_1687_, 2);
lean_inc(v_d_1736_);
lean_dec_ref_known(v_t_1687_, 3);
v___x_1737_ = lean_apply_2(v_costing_1701_, v_cost_1735_, v_d_1736_);
return v___x_1737_;
}
case 14:
{
lean_object* v_a_1738_; lean_object* v_b_1739_; lean_object* v___x_1740_; 
lean_dec(v_append_1703_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_a_1738_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_a_1738_);
v_b_1739_ = lean_ctor_get(v_t_1687_, 2);
lean_inc(v_b_1739_);
lean_dec_ref_known(v_t_1687_, 3);
v___x_1740_ = lean_apply_2(v_either_1702_, v_a_1738_, v_b_1739_);
return v___x_1740_;
}
default: 
{
lean_object* v_a_1741_; lean_object* v_b_1742_; lean_object* v___x_1743_; 
lean_dec(v_either_1702_);
lean_dec(v_costing_1701_);
lean_dec(v_guarded_1700_);
lean_dec(v_free_1699_);
lean_dec(v_initial_1698_);
lean_dec(v_final_1697_);
lean_dec(v_unindented_1696_);
lean_dec(v_aligned_1695_);
lean_dec(v_indented_1694_);
lean_dec(v_unflattenable_1693_);
lean_dec(v_flattened_1692_);
lean_dec(v_tagged_1691_);
lean_dec(v_text_1690_);
lean_dec(v_newline_1689_);
v_a_1741_ = lean_ctor_get(v_t_1687_, 1);
lean_inc(v_a_1741_);
v_b_1742_ = lean_ctor_get(v_t_1687_, 2);
lean_inc(v_b_1742_);
lean_dec_ref_known(v_t_1687_, 3);
v___x_1743_ = lean_apply_2(v_append_1703_, v_a_1741_, v_b_1742_);
return v___x_1743_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg___boxed(lean_object** _args){
lean_object* v_t_1744_ = _args[0];
lean_object* v_failure_1745_ = _args[1];
lean_object* v_newline_1746_ = _args[2];
lean_object* v_text_1747_ = _args[3];
lean_object* v_tagged_1748_ = _args[4];
lean_object* v_flattened_1749_ = _args[5];
lean_object* v_unflattenable_1750_ = _args[6];
lean_object* v_indented_1751_ = _args[7];
lean_object* v_aligned_1752_ = _args[8];
lean_object* v_unindented_1753_ = _args[9];
lean_object* v_final_1754_ = _args[10];
lean_object* v_initial_1755_ = _args[11];
lean_object* v_free_1756_ = _args[12];
lean_object* v_guarded_1757_ = _args[13];
lean_object* v_costing_1758_ = _args[14];
lean_object* v_either_1759_ = _args[15];
lean_object* v_append_1760_ = _args[16];
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Fmt_Doc_casesOn___override___redArg(v_t_1744_, v_failure_1745_, v_newline_1746_, v_text_1747_, v_tagged_1748_, v_flattened_1749_, v_unflattenable_1750_, v_indented_1751_, v_aligned_1752_, v_unindented_1753_, v_final_1754_, v_initial_1755_, v_free_1756_, v_guarded_1757_, v_costing_1758_, v_either_1759_, v_append_1760_);
lean_dec(v_failure_1745_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override(lean_object* v_00_u03c4_1762_, lean_object* v_motive_1763_, lean_object* v_t_1764_, lean_object* v_failure_1765_, lean_object* v_newline_1766_, lean_object* v_text_1767_, lean_object* v_tagged_1768_, lean_object* v_flattened_1769_, lean_object* v_unflattenable_1770_, lean_object* v_indented_1771_, lean_object* v_aligned_1772_, lean_object* v_unindented_1773_, lean_object* v_final_1774_, lean_object* v_initial_1775_, lean_object* v_free_1776_, lean_object* v_guarded_1777_, lean_object* v_costing_1778_, lean_object* v_either_1779_, lean_object* v_append_1780_){
_start:
{
switch(lean_obj_tag(v_t_1764_))
{
case 0:
{
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
lean_inc(v_failure_1765_);
return v_failure_1765_;
}
case 1:
{
lean_object* v_f_1781_; lean_object* v___x_1782_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
v_f_1781_ = lean_ctor_get(v_t_1764_, 1);
lean_inc_ref(v_f_1781_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1782_ = lean_apply_1(v_newline_1766_, v_f_1781_);
return v___x_1782_;
}
case 2:
{
lean_object* v_s_1783_; lean_object* v___x_1784_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_newline_1766_);
v_s_1783_ = lean_ctor_get(v_t_1764_, 1);
lean_inc_ref(v_s_1783_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1784_ = lean_apply_1(v_text_1767_, v_s_1783_);
return v___x_1784_;
}
case 3:
{
lean_object* v_id_1785_; lean_object* v_d_1786_; lean_object* v___x_1787_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_id_1785_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_id_1785_);
v_d_1786_ = lean_ctor_get(v_t_1764_, 2);
lean_inc(v_d_1786_);
lean_dec_ref_known(v_t_1764_, 3);
v___x_1787_ = lean_apply_2(v_tagged_1768_, v_id_1785_, v_d_1786_);
return v___x_1787_;
}
case 4:
{
lean_object* v_d_1788_; lean_object* v___x_1789_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_d_1788_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_d_1788_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1789_ = lean_apply_1(v_flattened_1769_, v_d_1788_);
return v___x_1789_;
}
case 5:
{
lean_object* v_d_1790_; lean_object* v___x_1791_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_d_1790_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_d_1790_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1791_ = lean_apply_1(v_unflattenable_1770_, v_d_1790_);
return v___x_1791_;
}
case 6:
{
lean_object* v_n_1792_; uint8_t v_isCumulative_1793_; lean_object* v_d_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_n_1792_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_n_1792_);
v_isCumulative_1793_ = lean_ctor_get_uint8(v_t_1764_, sizeof(void*)*3 + 7);
v_d_1794_ = lean_ctor_get(v_t_1764_, 2);
lean_inc(v_d_1794_);
lean_dec_ref_known(v_t_1764_, 3);
v___x_1795_ = lean_box(v_isCumulative_1793_);
v___x_1796_ = lean_apply_3(v_indented_1771_, v_n_1792_, v___x_1795_, v_d_1794_);
return v___x_1796_;
}
case 7:
{
lean_object* v_d_1797_; lean_object* v___x_1798_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_d_1797_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_d_1797_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1798_ = lean_apply_1(v_aligned_1772_, v_d_1797_);
return v___x_1798_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1799_; lean_object* v_d_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_onlyNonCumulative_1799_ = lean_ctor_get_uint8(v_t_1764_, sizeof(void*)*2 + 7);
v_d_1800_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_d_1800_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1801_ = lean_box(v_onlyNonCumulative_1799_);
v___x_1802_ = lean_apply_2(v_unindented_1773_, v___x_1801_, v_d_1800_);
return v___x_1802_;
}
case 9:
{
lean_object* v_d_1803_; lean_object* v___x_1804_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_d_1803_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_d_1803_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1804_ = lean_apply_1(v_final_1774_, v_d_1803_);
return v___x_1804_;
}
case 10:
{
lean_object* v_d_1805_; lean_object* v___x_1806_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_d_1805_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_d_1805_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1806_ = lean_apply_1(v_initial_1775_, v_d_1805_);
return v___x_1806_;
}
case 11:
{
lean_object* v_d_1807_; lean_object* v___x_1808_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_d_1807_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_d_1807_);
lean_dec_ref_known(v_t_1764_, 2);
v___x_1808_ = lean_apply_1(v_free_1776_, v_d_1807_);
return v___x_1808_;
}
case 12:
{
lean_object* v_p_1809_; lean_object* v_d_1810_; lean_object* v___x_1811_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_p_1809_ = lean_ctor_get(v_t_1764_, 1);
lean_inc_ref(v_p_1809_);
v_d_1810_ = lean_ctor_get(v_t_1764_, 2);
lean_inc(v_d_1810_);
lean_dec_ref_known(v_t_1764_, 3);
v___x_1811_ = lean_apply_2(v_guarded_1777_, v_p_1809_, v_d_1810_);
return v___x_1811_;
}
case 13:
{
lean_object* v_cost_1812_; lean_object* v_d_1813_; lean_object* v___x_1814_; 
lean_dec(v_append_1780_);
lean_dec(v_either_1779_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_cost_1812_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_cost_1812_);
v_d_1813_ = lean_ctor_get(v_t_1764_, 2);
lean_inc(v_d_1813_);
lean_dec_ref_known(v_t_1764_, 3);
v___x_1814_ = lean_apply_2(v_costing_1778_, v_cost_1812_, v_d_1813_);
return v___x_1814_;
}
case 14:
{
lean_object* v_a_1815_; lean_object* v_b_1816_; lean_object* v___x_1817_; 
lean_dec(v_append_1780_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_a_1815_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_a_1815_);
v_b_1816_ = lean_ctor_get(v_t_1764_, 2);
lean_inc(v_b_1816_);
lean_dec_ref_known(v_t_1764_, 3);
v___x_1817_ = lean_apply_2(v_either_1779_, v_a_1815_, v_b_1816_);
return v___x_1817_;
}
default: 
{
lean_object* v_a_1818_; lean_object* v_b_1819_; lean_object* v___x_1820_; 
lean_dec(v_either_1779_);
lean_dec(v_costing_1778_);
lean_dec(v_guarded_1777_);
lean_dec(v_free_1776_);
lean_dec(v_initial_1775_);
lean_dec(v_final_1774_);
lean_dec(v_unindented_1773_);
lean_dec(v_aligned_1772_);
lean_dec(v_indented_1771_);
lean_dec(v_unflattenable_1770_);
lean_dec(v_flattened_1769_);
lean_dec(v_tagged_1768_);
lean_dec(v_text_1767_);
lean_dec(v_newline_1766_);
v_a_1818_ = lean_ctor_get(v_t_1764_, 1);
lean_inc(v_a_1818_);
v_b_1819_ = lean_ctor_get(v_t_1764_, 2);
lean_inc(v_b_1819_);
lean_dec_ref_known(v_t_1764_, 3);
v___x_1820_ = lean_apply_2(v_append_1780_, v_a_1818_, v_b_1819_);
return v___x_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___boxed(lean_object** _args){
lean_object* v_00_u03c4_1821_ = _args[0];
lean_object* v_motive_1822_ = _args[1];
lean_object* v_t_1823_ = _args[2];
lean_object* v_failure_1824_ = _args[3];
lean_object* v_newline_1825_ = _args[4];
lean_object* v_text_1826_ = _args[5];
lean_object* v_tagged_1827_ = _args[6];
lean_object* v_flattened_1828_ = _args[7];
lean_object* v_unflattenable_1829_ = _args[8];
lean_object* v_indented_1830_ = _args[9];
lean_object* v_aligned_1831_ = _args[10];
lean_object* v_unindented_1832_ = _args[11];
lean_object* v_final_1833_ = _args[12];
lean_object* v_initial_1834_ = _args[13];
lean_object* v_free_1835_ = _args[14];
lean_object* v_guarded_1836_ = _args[15];
lean_object* v_costing_1837_ = _args[16];
lean_object* v_either_1838_ = _args[17];
lean_object* v_append_1839_ = _args[18];
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_Fmt_Doc_casesOn___override(v_00_u03c4_1821_, v_motive_1822_, v_t_1823_, v_failure_1824_, v_newline_1825_, v_text_1826_, v_tagged_1827_, v_flattened_1828_, v_unflattenable_1829_, v_indented_1830_, v_aligned_1831_, v_unindented_1832_, v_final_1833_, v_initial_1834_, v_free_1835_, v_guarded_1836_, v_costing_1837_, v_either_1838_, v_append_1839_);
lean_dec(v_failure_1824_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg(){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_box(0);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override___redArg___boxed(lean_object* v___dummy_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Fmt_Doc_failure___override___redArg();
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override(lean_object* v_00_u03c4_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_box(0);
return v___x_1846_;
}
}
static uint16_t _init_l_Lean_Fmt_Doc_newline___override___redArg___closed__1(void){
_start:
{
uint16_t v___x_1849_; uint16_t v___x_1850_; 
v___x_1849_ = l_Lean_Fmt_newlineFailureSet;
v___x_1850_ = lean_uint16_complement(v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object* v_f_1851_){
_start:
{
uint16_t v___x_1852_; lean_object* v___x_1853_; uint8_t v___y_1855_; uint8_t v___y_1856_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; uint8_t v___y_1864_; 
v___x_1852_ = l_Lean_Fmt_newlineFailureSet;
v___x_1853_ = ((lean_object*)(l_Lean_Fmt_Doc_newline___override___redArg___closed__0));
v___x_1860_ = lean_string_utf8_byte_size(v_f_1851_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_nat_dec_eq(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
uint8_t v___x_1867_; 
v___x_1867_ = 2;
v___y_1864_ = v___x_1867_;
goto v___jp_1863_;
}
else
{
uint8_t v___x_1868_; 
v___x_1868_ = 1;
v___y_1864_ = v___x_1868_;
goto v___jp_1863_;
}
v___jp_1854_:
{
uint8_t v___x_1857_; uint16_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = 1;
v___x_1858_ = lean_uint16_once(&l_Lean_Fmt_Doc_newline___override___redArg___closed__1, &l_Lean_Fmt_Doc_newline___override___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_newline___override___redArg___closed__1);
v___x_1859_ = lean_alloc_ctor(1, 2, 7);
lean_ctor_set(v___x_1859_, 0, v___x_1853_);
lean_ctor_set(v___x_1859_, 1, v_f_1851_);
lean_ctor_set_uint16(v___x_1859_, sizeof(void*)*2, v___x_1852_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*2 + 4, v___y_1855_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*2 + 5, v___y_1856_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*2 + 6, v___x_1857_);
lean_ctor_set_uint16(v___x_1859_, sizeof(void*)*2 + 2, v___x_1858_);
return v___x_1859_;
}
v___jp_1863_:
{
if (v___x_1862_ == 0)
{
uint8_t v___x_1865_; 
v___x_1865_ = 0;
v___y_1855_ = v___y_1864_;
v___y_1856_ = v___x_1865_;
goto v___jp_1854_;
}
else
{
uint8_t v___x_1866_; 
v___x_1866_ = 1;
v___y_1855_ = v___y_1864_;
v___y_1856_ = v___x_1866_;
goto v___jp_1854_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object* v_00_u03c4_1869_, lean_object* v_f_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Fmt_Doc_newline___override___redArg(v_f_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object* v_s_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; uint16_t v___x_1878_; lean_object* v___x_1879_; uint8_t v___y_1881_; uint8_t v___y_1882_; uint8_t v___y_1887_; 
v___x_1875_ = lean_string_utf8_byte_size(v_s_1874_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_nat_dec_eq(v___x_1875_, v___x_1876_);
v___x_1878_ = l_Lean_Fmt_textFailureSet(v___x_1877_);
v___x_1879_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
if (v___x_1877_ == 0)
{
uint8_t v___x_1890_; 
v___x_1890_ = 2;
v___y_1887_ = v___x_1890_;
goto v___jp_1886_;
}
else
{
uint8_t v___x_1891_; 
v___x_1891_ = 0;
v___y_1887_ = v___x_1891_;
goto v___jp_1886_;
}
v___jp_1880_:
{
uint8_t v___x_1883_; uint16_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = 0;
v___x_1884_ = lean_uint16_complement(v___x_1878_);
v___x_1885_ = lean_alloc_ctor(2, 2, 7);
lean_ctor_set(v___x_1885_, 0, v___x_1879_);
lean_ctor_set(v___x_1885_, 1, v_s_1874_);
lean_ctor_set_uint16(v___x_1885_, sizeof(void*)*2, v___x_1878_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*2 + 4, v___y_1881_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*2 + 5, v___y_1882_);
lean_ctor_set_uint8(v___x_1885_, sizeof(void*)*2 + 6, v___x_1883_);
lean_ctor_set_uint16(v___x_1885_, sizeof(void*)*2 + 2, v___x_1884_);
return v___x_1885_;
}
v___jp_1886_:
{
if (v___x_1877_ == 0)
{
uint8_t v___x_1888_; 
v___x_1888_ = 0;
v___y_1881_ = v___y_1887_;
v___y_1882_ = v___x_1888_;
goto v___jp_1880_;
}
else
{
uint8_t v___x_1889_; 
v___x_1889_ = 1;
v___y_1881_ = v___y_1887_;
v___y_1882_ = v___x_1889_;
goto v___jp_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object* v_00_u03c4_1892_, lean_object* v_s_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object* v_x_1895_){
_start:
{
switch(lean_obj_tag(v_x_1895_))
{
case 0:
{
uint8_t v___x_1896_; 
v___x_1896_ = 0;
return v___x_1896_;
}
case 3:
{
uint8_t v_atomicness_1897_; 
v_atomicness_1897_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 6);
return v_atomicness_1897_;
}
case 6:
{
uint8_t v_atomicness_1898_; 
v_atomicness_1898_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 6);
return v_atomicness_1898_;
}
case 12:
{
uint8_t v_atomicness_1899_; 
v_atomicness_1899_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 6);
return v_atomicness_1899_;
}
case 13:
{
uint8_t v_atomicness_1900_; 
v_atomicness_1900_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 6);
return v_atomicness_1900_;
}
case 14:
{
uint8_t v_atomicness_1901_; 
v_atomicness_1901_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 6);
return v_atomicness_1901_;
}
case 15:
{
uint8_t v_atomicness_1902_; 
v_atomicness_1902_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*3 + 6);
return v_atomicness_1902_;
}
default: 
{
uint8_t v_atomicness_1903_; 
v_atomicness_1903_ = lean_ctor_get_uint8(v_x_1895_, sizeof(void*)*2 + 6);
return v_atomicness_1903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object* v_x_1904_){
_start:
{
uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_res_1905_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_1904_);
lean_dec(v_x_1904_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object* v_x_1907_){
_start:
{
if (lean_obj_tag(v_x_1907_) == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_box(0);
return v___x_1908_;
}
else
{
lean_object* v_maxNewlineCount_x3f_1909_; 
v_maxNewlineCount_x3f_1909_ = lean_ctor_get(v_x_1907_, 0);
lean_inc(v_maxNewlineCount_x3f_1909_);
return v_maxNewlineCount_x3f_1909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object* v_x_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_1910_);
lean_dec(v_x_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object* v_x_1912_){
_start:
{
switch(lean_obj_tag(v_x_1912_))
{
case 0:
{
uint8_t v___x_1913_; 
v___x_1913_ = 1;
return v___x_1913_;
}
case 3:
{
uint8_t v_alwaysNonEmptiness_1914_; 
v_alwaysNonEmptiness_1914_ = lean_ctor_get_uint8(v_x_1912_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1914_;
}
case 6:
{
uint8_t v_alwaysNonEmptiness_1915_; 
v_alwaysNonEmptiness_1915_ = lean_ctor_get_uint8(v_x_1912_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1915_;
}
case 12:
{
uint8_t v_alwaysNonEmptiness_1916_; 
v_alwaysNonEmptiness_1916_ = lean_ctor_get_uint8(v_x_1912_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1916_;
}
case 13:
{
uint8_t v_alwaysNonEmptiness_1917_; 
v_alwaysNonEmptiness_1917_ = lean_ctor_get_uint8(v_x_1912_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1917_;
}
case 14:
{
uint8_t v_alwaysNonEmptiness_1918_; 
v_alwaysNonEmptiness_1918_ = lean_ctor_get_uint8(v_x_1912_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1918_;
}
case 15:
{
uint8_t v_alwaysNonEmptiness_1919_; 
v_alwaysNonEmptiness_1919_ = lean_ctor_get_uint8(v_x_1912_, sizeof(void*)*3 + 5);
return v_alwaysNonEmptiness_1919_;
}
default: 
{
uint8_t v_alwaysNonEmptiness_1920_; 
v_alwaysNonEmptiness_1920_ = lean_ctor_get_uint8(v_x_1912_, sizeof(void*)*2 + 5);
return v_alwaysNonEmptiness_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object* v_x_1921_){
_start:
{
uint8_t v_res_1922_; lean_object* v_r_1923_; 
v_res_1922_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_1921_);
lean_dec(v_x_1921_);
v_r_1923_ = lean_box(v_res_1922_);
return v_r_1923_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override___redArg(lean_object* v_x_1924_){
_start:
{
switch(lean_obj_tag(v_x_1924_))
{
case 0:
{
uint16_t v___x_1925_; 
v___x_1925_ = 0;
return v___x_1925_;
}
case 3:
{
uint16_t v_neverFailsSet_1926_; 
v_neverFailsSet_1926_ = lean_ctor_get_uint16(v_x_1924_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1926_;
}
case 6:
{
uint16_t v_neverFailsSet_1927_; 
v_neverFailsSet_1927_ = lean_ctor_get_uint16(v_x_1924_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1927_;
}
case 12:
{
uint16_t v_neverFailsSet_1928_; 
v_neverFailsSet_1928_ = lean_ctor_get_uint16(v_x_1924_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1928_;
}
case 13:
{
uint16_t v_neverFailsSet_1929_; 
v_neverFailsSet_1929_ = lean_ctor_get_uint16(v_x_1924_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1929_;
}
case 14:
{
uint16_t v_neverFailsSet_1930_; 
v_neverFailsSet_1930_ = lean_ctor_get_uint16(v_x_1924_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1930_;
}
case 15:
{
uint16_t v_neverFailsSet_1931_; 
v_neverFailsSet_1931_ = lean_ctor_get_uint16(v_x_1924_, sizeof(void*)*3 + 2);
return v_neverFailsSet_1931_;
}
default: 
{
uint16_t v_neverFailsSet_1932_; 
v_neverFailsSet_1932_ = lean_ctor_get_uint16(v_x_1924_, sizeof(void*)*2 + 2);
return v_neverFailsSet_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___redArg___boxed(lean_object* v_x_1933_){
_start:
{
uint16_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_x_1933_);
lean_dec(v_x_1933_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object* v_x_1936_){
_start:
{
switch(lean_obj_tag(v_x_1936_))
{
case 0:
{
uint8_t v___x_1937_; 
v___x_1937_ = 2;
return v___x_1937_;
}
case 3:
{
uint8_t v_alwaysEmptiness_1938_; 
v_alwaysEmptiness_1938_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1938_;
}
case 6:
{
uint8_t v_alwaysEmptiness_1939_; 
v_alwaysEmptiness_1939_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1939_;
}
case 12:
{
uint8_t v_alwaysEmptiness_1940_; 
v_alwaysEmptiness_1940_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1940_;
}
case 13:
{
uint8_t v_alwaysEmptiness_1941_; 
v_alwaysEmptiness_1941_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1941_;
}
case 14:
{
uint8_t v_alwaysEmptiness_1942_; 
v_alwaysEmptiness_1942_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1942_;
}
case 15:
{
uint8_t v_alwaysEmptiness_1943_; 
v_alwaysEmptiness_1943_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*3 + 4);
return v_alwaysEmptiness_1943_;
}
default: 
{
uint8_t v_alwaysEmptiness_1944_; 
v_alwaysEmptiness_1944_ = lean_ctor_get_uint8(v_x_1936_, sizeof(void*)*2 + 4);
return v_alwaysEmptiness_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object* v_x_1945_){
_start:
{
uint8_t v_res_1946_; lean_object* v_r_1947_; 
v_res_1946_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_1945_);
lean_dec(v_x_1945_);
v_r_1947_ = lean_box(v_res_1946_);
return v_r_1947_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override___redArg(lean_object* v_x_1948_){
_start:
{
switch(lean_obj_tag(v_x_1948_))
{
case 0:
{
uint16_t v___x_1949_; 
v___x_1949_ = 65535;
return v___x_1949_;
}
case 3:
{
uint16_t v_failureSet_1950_; 
v_failureSet_1950_ = lean_ctor_get_uint16(v_x_1948_, sizeof(void*)*3);
return v_failureSet_1950_;
}
case 6:
{
uint16_t v_failureSet_1951_; 
v_failureSet_1951_ = lean_ctor_get_uint16(v_x_1948_, sizeof(void*)*3);
return v_failureSet_1951_;
}
case 12:
{
uint16_t v_failureSet_1952_; 
v_failureSet_1952_ = lean_ctor_get_uint16(v_x_1948_, sizeof(void*)*3);
return v_failureSet_1952_;
}
case 13:
{
uint16_t v_failureSet_1953_; 
v_failureSet_1953_ = lean_ctor_get_uint16(v_x_1948_, sizeof(void*)*3);
return v_failureSet_1953_;
}
case 14:
{
uint16_t v_failureSet_1954_; 
v_failureSet_1954_ = lean_ctor_get_uint16(v_x_1948_, sizeof(void*)*3);
return v_failureSet_1954_;
}
case 15:
{
uint16_t v_failureSet_1955_; 
v_failureSet_1955_ = lean_ctor_get_uint16(v_x_1948_, sizeof(void*)*3);
return v_failureSet_1955_;
}
default: 
{
uint16_t v_failureSet_1956_; 
v_failureSet_1956_ = lean_ctor_get_uint16(v_x_1948_, sizeof(void*)*2);
return v_failureSet_1956_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___redArg___boxed(lean_object* v_x_1957_){
_start:
{
uint16_t v_res_1958_; lean_object* v_r_1959_; 
v_res_1958_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_x_1957_);
lean_dec(v_x_1957_);
v_r_1959_ = lean_box(v_res_1958_);
return v_r_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object* v_id_1960_, lean_object* v_d_1961_){
_start:
{
uint16_t v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; uint8_t v___x_1965_; uint8_t v___x_1966_; uint16_t v___x_1967_; lean_object* v___x_1968_; 
v___x_1962_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_1961_);
v___x_1963_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1961_);
v___x_1964_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1961_);
v___x_1965_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1961_);
v___x_1966_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1961_);
v___x_1967_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_1961_);
v___x_1968_ = lean_alloc_ctor(3, 3, 7);
lean_ctor_set(v___x_1968_, 0, v___x_1963_);
lean_ctor_set(v___x_1968_, 1, v_id_1960_);
lean_ctor_set(v___x_1968_, 2, v_d_1961_);
lean_ctor_set_uint16(v___x_1968_, sizeof(void*)*3, v___x_1962_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*3 + 4, v___x_1964_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*3 + 5, v___x_1965_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*3 + 6, v___x_1966_);
lean_ctor_set_uint16(v___x_1968_, sizeof(void*)*3 + 2, v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object* v_00_u03c4_1969_, lean_object* v_id_1970_, lean_object* v_d_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_id_1970_, v_d_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object* v_d_1973_){
_start:
{
uint16_t v___x_1974_; lean_object* v___x_1975_; uint8_t v___y_1977_; uint8_t v___x_1985_; 
v___x_1974_ = 0;
v___x_1975_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
v___x_1985_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1973_);
if (v___x_1985_ == 1)
{
uint8_t v___x_1986_; 
v___x_1986_ = 0;
v___y_1977_ = v___x_1986_;
goto v___jp_1976_;
}
else
{
v___y_1977_ = v___x_1985_;
goto v___jp_1976_;
}
v___jp_1976_:
{
uint8_t v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1973_);
v___x_1979_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1973_);
switch(v___x_1979_)
{
case 1:
{
uint8_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = 0;
v___x_1981_ = lean_alloc_ctor(4, 2, 7);
lean_ctor_set(v___x_1981_, 0, v___x_1975_);
lean_ctor_set(v___x_1981_, 1, v_d_1973_);
lean_ctor_set_uint16(v___x_1981_, sizeof(void*)*2, v___x_1974_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*2 + 4, v___y_1977_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*2 + 5, v___x_1978_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*2 + 6, v___x_1980_);
lean_ctor_set_uint16(v___x_1981_, sizeof(void*)*2 + 2, v___x_1974_);
return v___x_1981_;
}
case 3:
{
uint8_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = 2;
v___x_1983_ = lean_alloc_ctor(4, 2, 7);
lean_ctor_set(v___x_1983_, 0, v___x_1975_);
lean_ctor_set(v___x_1983_, 1, v_d_1973_);
lean_ctor_set_uint16(v___x_1983_, sizeof(void*)*2, v___x_1974_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*2 + 4, v___y_1977_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*2 + 5, v___x_1978_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*2 + 6, v___x_1982_);
lean_ctor_set_uint16(v___x_1983_, sizeof(void*)*2 + 2, v___x_1974_);
return v___x_1983_;
}
default: 
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_alloc_ctor(4, 2, 7);
lean_ctor_set(v___x_1984_, 0, v___x_1975_);
lean_ctor_set(v___x_1984_, 1, v_d_1973_);
lean_ctor_set_uint16(v___x_1984_, sizeof(void*)*2, v___x_1974_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2 + 4, v___y_1977_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2 + 5, v___x_1978_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*2 + 6, v___x_1979_);
lean_ctor_set_uint16(v___x_1984_, sizeof(void*)*2 + 2, v___x_1974_);
return v___x_1984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override(lean_object* v_00_u03c4_1987_, lean_object* v_d_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object* v_d_1990_){
_start:
{
uint16_t v___x_1991_; lean_object* v___x_1992_; uint8_t v___y_1994_; uint8_t v___x_2002_; 
v___x_1991_ = 0;
v___x_1992_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1990_);
v___x_2002_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1990_);
if (v___x_2002_ == 1)
{
uint8_t v___x_2003_; 
v___x_2003_ = 2;
v___y_1994_ = v___x_2003_;
goto v___jp_1993_;
}
else
{
v___y_1994_ = v___x_2002_;
goto v___jp_1993_;
}
v___jp_1993_:
{
uint8_t v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1990_);
v___x_1996_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1990_);
switch(v___x_1996_)
{
case 1:
{
uint8_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = 4;
v___x_1998_ = lean_alloc_ctor(5, 2, 7);
lean_ctor_set(v___x_1998_, 0, v___x_1992_);
lean_ctor_set(v___x_1998_, 1, v_d_1990_);
lean_ctor_set_uint16(v___x_1998_, sizeof(void*)*2, v___x_1991_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*2 + 4, v___y_1994_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*2 + 5, v___x_1995_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*2 + 6, v___x_1997_);
lean_ctor_set_uint16(v___x_1998_, sizeof(void*)*2 + 2, v___x_1991_);
return v___x_1998_;
}
case 3:
{
uint8_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = 4;
v___x_2000_ = lean_alloc_ctor(5, 2, 7);
lean_ctor_set(v___x_2000_, 0, v___x_1992_);
lean_ctor_set(v___x_2000_, 1, v_d_1990_);
lean_ctor_set_uint16(v___x_2000_, sizeof(void*)*2, v___x_1991_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*2 + 4, v___y_1994_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*2 + 5, v___x_1995_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*2 + 6, v___x_1999_);
lean_ctor_set_uint16(v___x_2000_, sizeof(void*)*2 + 2, v___x_1991_);
return v___x_2000_;
}
default: 
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(5, 2, 7);
lean_ctor_set(v___x_2001_, 0, v___x_1992_);
lean_ctor_set(v___x_2001_, 1, v_d_1990_);
lean_ctor_set_uint16(v___x_2001_, sizeof(void*)*2, v___x_1991_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*2 + 4, v___y_1994_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*2 + 5, v___x_1995_);
lean_ctor_set_uint8(v___x_2001_, sizeof(void*)*2 + 6, v___x_1996_);
lean_ctor_set_uint16(v___x_2001_, sizeof(void*)*2 + 2, v___x_1991_);
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override(lean_object* v_00_u03c4_2004_, lean_object* v_d_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v_d_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg(lean_object* v_n_2007_, uint8_t v_isCumulative_2008_, lean_object* v_d_2009_){
_start:
{
uint16_t v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; uint8_t v___x_2013_; uint8_t v___x_2014_; uint16_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2010_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2009_);
v___x_2011_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2009_);
v___x_2012_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2009_);
v___x_2013_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2009_);
v___x_2014_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2009_);
v___x_2015_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2009_);
v___x_2016_ = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(v___x_2016_, 0, v___x_2011_);
lean_ctor_set(v___x_2016_, 1, v_n_2007_);
lean_ctor_set(v___x_2016_, 2, v_d_2009_);
lean_ctor_set_uint16(v___x_2016_, sizeof(void*)*3, v___x_2010_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*3 + 4, v___x_2012_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*3 + 5, v___x_2013_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*3 + 6, v___x_2014_);
lean_ctor_set_uint16(v___x_2016_, sizeof(void*)*3 + 2, v___x_2015_);
lean_ctor_set_uint8(v___x_2016_, sizeof(void*)*3 + 7, v_isCumulative_2008_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg___boxed(lean_object* v_n_2017_, lean_object* v_isCumulative_2018_, lean_object* v_d_2019_){
_start:
{
uint8_t v_isCumulative_boxed_2020_; lean_object* v_res_2021_; 
v_isCumulative_boxed_2020_ = lean_unbox(v_isCumulative_2018_);
v_res_2021_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_2017_, v_isCumulative_boxed_2020_, v_d_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override(lean_object* v_00_u03c4_2022_, lean_object* v_n_2023_, uint8_t v_isCumulative_2024_, lean_object* v_d_2025_){
_start:
{
lean_object* v___x_2026_; 
v___x_2026_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_2023_, v_isCumulative_2024_, v_d_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___boxed(lean_object* v_00_u03c4_2027_, lean_object* v_n_2028_, lean_object* v_isCumulative_2029_, lean_object* v_d_2030_){
_start:
{
uint8_t v_isCumulative_boxed_2031_; lean_object* v_res_2032_; 
v_isCumulative_boxed_2031_ = lean_unbox(v_isCumulative_2029_);
v_res_2032_ = l_Lean_Fmt_Doc_indented___override(v_00_u03c4_2027_, v_n_2028_, v_isCumulative_boxed_2031_, v_d_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object* v_d_2033_){
_start:
{
uint16_t v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; uint8_t v___x_2037_; uint8_t v___x_2038_; uint16_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2034_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2033_);
v___x_2035_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2033_);
v___x_2036_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2033_);
v___x_2037_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2033_);
v___x_2038_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2033_);
v___x_2039_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2033_);
v___x_2040_ = lean_alloc_ctor(7, 2, 7);
lean_ctor_set(v___x_2040_, 0, v___x_2035_);
lean_ctor_set(v___x_2040_, 1, v_d_2033_);
lean_ctor_set_uint16(v___x_2040_, sizeof(void*)*2, v___x_2034_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*2 + 4, v___x_2036_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*2 + 5, v___x_2037_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*2 + 6, v___x_2038_);
lean_ctor_set_uint16(v___x_2040_, sizeof(void*)*2 + 2, v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override(lean_object* v_00_u03c4_2041_, lean_object* v_d_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_d_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t v_onlyNonCumulative_2044_, lean_object* v_d_2045_){
_start:
{
uint16_t v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; uint8_t v___x_2049_; uint8_t v___x_2050_; uint16_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2046_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2045_);
v___x_2047_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2045_);
v___x_2048_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2045_);
v___x_2049_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2045_);
v___x_2050_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2045_);
v___x_2051_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2045_);
v___x_2052_ = lean_alloc_ctor(8, 2, 8);
lean_ctor_set(v___x_2052_, 0, v___x_2047_);
lean_ctor_set(v___x_2052_, 1, v_d_2045_);
lean_ctor_set_uint16(v___x_2052_, sizeof(void*)*2, v___x_2046_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*2 + 4, v___x_2048_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*2 + 5, v___x_2049_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*2 + 6, v___x_2050_);
lean_ctor_set_uint16(v___x_2052_, sizeof(void*)*2 + 2, v___x_2051_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*2 + 7, v_onlyNonCumulative_2044_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg___boxed(lean_object* v_onlyNonCumulative_2053_, lean_object* v_d_2054_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_2055_; lean_object* v_res_2056_; 
v_onlyNonCumulative_boxed_2055_ = lean_unbox(v_onlyNonCumulative_2053_);
v_res_2056_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_boxed_2055_, v_d_2054_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override(lean_object* v_00_u03c4_2057_, uint8_t v_onlyNonCumulative_2058_, lean_object* v_d_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_2058_, v_d_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___boxed(lean_object* v_00_u03c4_2061_, lean_object* v_onlyNonCumulative_2062_, lean_object* v_d_2063_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_2064_; lean_object* v_res_2065_; 
v_onlyNonCumulative_boxed_2064_ = lean_unbox(v_onlyNonCumulative_2062_);
v_res_2065_ = l_Lean_Fmt_Doc_unindented___override(v_00_u03c4_2061_, v_onlyNonCumulative_boxed_2064_, v_d_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object* v_d_2066_){
_start:
{
uint16_t v___x_2067_; uint16_t v___x_2068_; uint16_t v___x_2069_; uint16_t v___x_2070_; uint16_t v___x_2071_; uint16_t v___x_2072_; uint16_t v___x_2073_; uint16_t v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; uint8_t v___x_2078_; uint16_t v___x_2079_; uint16_t v___x_2080_; uint16_t v___x_2081_; uint16_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2067_ = 21845;
v___x_2068_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2066_);
v___x_2069_ = 1;
v___x_2070_ = lean_uint16_shift_left(v___x_2068_, v___x_2069_);
v___x_2071_ = lean_uint16_land(v___x_2070_, v___x_2068_);
v___x_2072_ = 43690;
v___x_2073_ = lean_uint16_land(v___x_2071_, v___x_2072_);
v___x_2074_ = lean_uint16_lor(v___x_2067_, v___x_2073_);
v___x_2075_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2066_);
v___x_2076_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2066_);
v___x_2077_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2066_);
v___x_2078_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2066_);
v___x_2079_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2066_);
v___x_2080_ = lean_uint16_shift_left(v___x_2079_, v___x_2069_);
v___x_2081_ = lean_uint16_lor(v___x_2080_, v___x_2079_);
v___x_2082_ = lean_uint16_land(v___x_2081_, v___x_2072_);
v___x_2083_ = lean_alloc_ctor(9, 2, 7);
lean_ctor_set(v___x_2083_, 0, v___x_2075_);
lean_ctor_set(v___x_2083_, 1, v_d_2066_);
lean_ctor_set_uint16(v___x_2083_, sizeof(void*)*2, v___x_2074_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2 + 4, v___x_2076_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2 + 5, v___x_2077_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2 + 6, v___x_2078_);
lean_ctor_set_uint16(v___x_2083_, sizeof(void*)*2 + 2, v___x_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override(lean_object* v_00_u03c4_2084_, lean_object* v_d_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Fmt_Doc_final___override___redArg(v_d_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object* v_d_2087_){
_start:
{
uint16_t v___x_2088_; uint16_t v___x_2089_; uint16_t v___x_2090_; uint16_t v___x_2091_; uint16_t v___x_2092_; uint16_t v___x_2093_; uint16_t v___x_2094_; uint16_t v___x_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; uint8_t v___x_2098_; uint8_t v___x_2099_; uint16_t v___x_2100_; uint16_t v___x_2101_; uint16_t v___x_2102_; uint16_t v___x_2103_; lean_object* v___x_2104_; 
v___x_2088_ = 255;
v___x_2089_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2087_);
v___x_2090_ = 8;
v___x_2091_ = lean_uint16_shift_left(v___x_2089_, v___x_2090_);
v___x_2092_ = lean_uint16_land(v___x_2091_, v___x_2089_);
v___x_2093_ = 65280;
v___x_2094_ = lean_uint16_land(v___x_2092_, v___x_2093_);
v___x_2095_ = lean_uint16_lor(v___x_2088_, v___x_2094_);
v___x_2096_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2087_);
v___x_2097_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2087_);
v___x_2098_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2087_);
v___x_2099_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2087_);
v___x_2100_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2087_);
v___x_2101_ = lean_uint16_shift_left(v___x_2100_, v___x_2090_);
v___x_2102_ = lean_uint16_lor(v___x_2101_, v___x_2100_);
v___x_2103_ = lean_uint16_land(v___x_2102_, v___x_2093_);
v___x_2104_ = lean_alloc_ctor(10, 2, 7);
lean_ctor_set(v___x_2104_, 0, v___x_2096_);
lean_ctor_set(v___x_2104_, 1, v_d_2087_);
lean_ctor_set_uint16(v___x_2104_, sizeof(void*)*2, v___x_2095_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*2 + 4, v___x_2097_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*2 + 5, v___x_2098_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*2 + 6, v___x_2099_);
lean_ctor_set_uint16(v___x_2104_, sizeof(void*)*2 + 2, v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override(lean_object* v_00_u03c4_2105_, lean_object* v_d_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Fmt_Doc_initial___override___redArg(v_d_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object* v_d_2108_){
_start:
{
uint16_t v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; uint16_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2109_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2108_);
v___x_2110_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2108_);
v___x_2111_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2108_);
v___x_2112_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2108_);
v___x_2113_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2108_);
v___x_2114_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2108_);
v___x_2115_ = lean_alloc_ctor(11, 2, 7);
lean_ctor_set(v___x_2115_, 0, v___x_2110_);
lean_ctor_set(v___x_2115_, 1, v_d_2108_);
lean_ctor_set_uint16(v___x_2115_, sizeof(void*)*2, v___x_2109_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*2 + 4, v___x_2111_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*2 + 5, v___x_2112_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*2 + 6, v___x_2113_);
lean_ctor_set_uint16(v___x_2115_, sizeof(void*)*2 + 2, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object* v_00_u03c4_2116_, lean_object* v_d_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_Fmt_Doc_free___override___redArg(v_d_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object* v_p_2119_, lean_object* v_d_2120_){
_start:
{
uint16_t v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; uint8_t v___x_2124_; uint8_t v___x_2125_; uint16_t v___x_2126_; lean_object* v___x_2127_; 
v___x_2121_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2120_);
v___x_2122_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2120_);
v___x_2123_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2120_);
v___x_2124_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2120_);
v___x_2125_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2120_);
v___x_2126_ = 0;
v___x_2127_ = lean_alloc_ctor(12, 3, 7);
lean_ctor_set(v___x_2127_, 0, v___x_2122_);
lean_ctor_set(v___x_2127_, 1, v_p_2119_);
lean_ctor_set(v___x_2127_, 2, v_d_2120_);
lean_ctor_set_uint16(v___x_2127_, sizeof(void*)*3, v___x_2121_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*3 + 4, v___x_2123_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*3 + 5, v___x_2124_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*3 + 6, v___x_2125_);
lean_ctor_set_uint16(v___x_2127_, sizeof(void*)*3 + 2, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object* v_00_u03c4_2128_, lean_object* v_p_2129_, lean_object* v_d_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_2129_, v_d_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object* v_cost_2132_, lean_object* v_d_2133_){
_start:
{
uint16_t v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; uint8_t v___x_2138_; uint16_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2134_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2133_);
v___x_2135_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_2133_);
v___x_2136_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2133_);
v___x_2137_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2133_);
v___x_2138_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2133_);
v___x_2139_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2133_);
v___x_2140_ = lean_alloc_ctor(13, 3, 7);
lean_ctor_set(v___x_2140_, 0, v___x_2135_);
lean_ctor_set(v___x_2140_, 1, v_cost_2132_);
lean_ctor_set(v___x_2140_, 2, v_d_2133_);
lean_ctor_set_uint16(v___x_2140_, sizeof(void*)*3, v___x_2134_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*3 + 4, v___x_2136_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*3 + 5, v___x_2137_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*3 + 6, v___x_2138_);
lean_ctor_set_uint16(v___x_2140_, sizeof(void*)*3 + 2, v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object* v_00_u03c4_2141_, lean_object* v_cost_2142_, lean_object* v_d_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Fmt_Doc_costing___override___redArg(v_cost_2142_, v_d_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0(lean_object* v_x1_2145_, lean_object* v_x2_2146_){
_start:
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_nat_dec_le(v_x1_2145_, v_x2_2146_);
if (v___x_2147_ == 0)
{
lean_inc(v_x1_2145_);
return v_x1_2145_;
}
else
{
lean_inc(v_x2_2146_);
return v_x2_2146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__0___boxed(lean_object* v_x1_2148_, lean_object* v_x2_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Fmt_Doc_either___override___redArg___lam__0(v_x1_2148_, v_x2_2149_);
lean_dec(v_x2_2149_);
lean_dec(v_x1_2148_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object* v_a_2152_, lean_object* v_b_2153_){
_start:
{
lean_object* v___f_2154_; uint16_t v___x_2155_; uint16_t v___x_2156_; uint16_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; uint8_t v___x_2162_; uint8_t v___x_2163_; uint8_t v___x_2164_; uint8_t v___x_2165_; uint8_t v___x_2166_; uint8_t v___x_2167_; uint16_t v___x_2168_; uint16_t v___x_2169_; uint16_t v___x_2170_; lean_object* v___x_2171_; 
v___f_2154_ = ((lean_object*)(l_Lean_Fmt_Doc_either___override___redArg___closed__0));
v___x_2155_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_a_2152_);
v___x_2156_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2153_);
v___x_2157_ = lean_uint16_land(v___x_2155_, v___x_2156_);
v___x_2158_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_2152_);
v___x_2159_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_2153_);
v___x_2160_ = l_Option_merge___redArg(v___f_2154_, v___x_2158_, v___x_2159_);
v___x_2161_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_2152_);
v___x_2162_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_2153_);
v___x_2163_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_2161_, v___x_2162_);
v___x_2164_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_2152_);
v___x_2165_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_2153_);
v___x_2166_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_2164_, v___x_2165_);
v___x_2167_ = 4;
v___x_2168_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_a_2152_);
v___x_2169_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2153_);
v___x_2170_ = lean_uint16_lor(v___x_2168_, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(14, 3, 7);
lean_ctor_set(v___x_2171_, 0, v___x_2160_);
lean_ctor_set(v___x_2171_, 1, v_a_2152_);
lean_ctor_set(v___x_2171_, 2, v_b_2153_);
lean_ctor_set_uint16(v___x_2171_, sizeof(void*)*3, v___x_2157_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 4, v___x_2163_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 5, v___x_2166_);
lean_ctor_set_uint8(v___x_2171_, sizeof(void*)*3 + 6, v___x_2167_);
lean_ctor_set_uint16(v___x_2171_, sizeof(void*)*3 + 2, v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object* v_00_u03c4_2172_, lean_object* v_a_2173_, lean_object* v_b_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_Fmt_Doc_either___override___redArg(v_a_2173_, v_b_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_failureSet___override(lean_object* v_00_u03c4_2176_, lean_object* v_x_2177_){
_start:
{
uint16_t v___x_2178_; 
v___x_2178_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failureSet___override___boxed(lean_object* v_00_u03c4_2179_, lean_object* v_x_2180_){
_start:
{
uint16_t v_res_2181_; lean_object* v_r_2182_; 
v_res_2181_ = l_Lean_Fmt_Doc_failureSet___override(v_00_u03c4_2179_, v_x_2180_);
lean_dec(v_x_2180_);
v_r_2182_ = lean_box(v_res_2181_);
return v_r_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object* v_00_u03c4_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object* v_00_u03c4_2186_, lean_object* v_x_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(v_00_u03c4_2186_, v_x_2187_);
lean_dec(v_x_2187_);
return v_res_2188_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object* v_00_u03c4_2189_, lean_object* v_x_2190_){
_start:
{
uint8_t v___x_2191_; 
v___x_2191_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object* v_00_u03c4_2192_, lean_object* v_x_2193_){
_start:
{
uint8_t v_res_2194_; lean_object* v_r_2195_; 
v_res_2194_ = l_Lean_Fmt_Doc_alwaysEmptiness___override(v_00_u03c4_2192_, v_x_2193_);
lean_dec(v_x_2193_);
v_r_2195_ = lean_box(v_res_2194_);
return v_r_2195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object* v_00_u03c4_2196_, lean_object* v_x_2197_){
_start:
{
uint8_t v___x_2198_; 
v___x_2198_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object* v_00_u03c4_2199_, lean_object* v_x_2200_){
_start:
{
uint8_t v_res_2201_; lean_object* v_r_2202_; 
v_res_2201_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override(v_00_u03c4_2199_, v_x_2200_);
lean_dec(v_x_2200_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object* v_00_u03c4_2203_, lean_object* v_x_2204_){
_start:
{
uint8_t v___x_2205_; 
v___x_2205_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object* v_00_u03c4_2206_, lean_object* v_x_2207_){
_start:
{
uint8_t v_res_2208_; lean_object* v_r_2209_; 
v_res_2208_ = l_Lean_Fmt_Doc_atomicness___override(v_00_u03c4_2206_, v_x_2207_);
lean_dec(v_x_2207_);
v_r_2209_ = lean_box(v_res_2208_);
return v_r_2209_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_Doc_neverFailsSet___override(lean_object* v_00_u03c4_2210_, lean_object* v_x_2211_){
_start:
{
uint16_t v___x_2212_; 
v___x_2212_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFailsSet___override___boxed(lean_object* v_00_u03c4_2213_, lean_object* v_x_2214_){
_start:
{
uint16_t v_res_2215_; lean_object* v_r_2216_; 
v_res_2215_ = l_Lean_Fmt_Doc_neverFailsSet___override(v_00_u03c4_2213_, v_x_2214_);
lean_dec(v_x_2214_);
v_r_2216_ = lean_box(v_res_2215_);
return v_r_2216_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(uint8_t v_s_2217_, uint16_t v___x_2218_, uint8_t v___y_2219_, lean_object* v_b_2220_, uint8_t v_isMidFull_2221_, uint8_t v_isMidInitial_2222_){
_start:
{
uint8_t v___x_2223_; uint8_t v___x_2224_; uint8_t v___x_2225_; uint8_t v___x_2226_; uint8_t v___x_2227_; uint8_t v___x_2228_; uint8_t v___x_2229_; uint8_t v___x_2230_; uint8_t v___x_2231_; uint8_t v___x_2232_; uint16_t v___x_2233_; uint16_t v___x_2234_; uint16_t v___x_2235_; uint16_t v___x_2236_; uint16_t v___x_2237_; uint8_t v___x_2238_; 
v___x_2223_ = 254;
v___x_2224_ = lean_uint8_land(v_s_2217_, v___x_2223_);
v___x_2225_ = lean_bool_to_uint8(v_isMidFull_2221_);
v___x_2226_ = lean_uint8_lor(v___x_2224_, v___x_2225_);
v___x_2227_ = 251;
v___x_2228_ = lean_uint8_land(v___x_2226_, v___x_2227_);
v___x_2229_ = lean_bool_to_uint8(v_isMidInitial_2222_);
v___x_2230_ = 2;
v___x_2231_ = lean_uint8_shift_left(v___x_2229_, v___x_2230_);
v___x_2232_ = lean_uint8_lor(v___x_2228_, v___x_2231_);
v___x_2233_ = lean_uint8_to_uint16(v___x_2232_);
v___x_2234_ = lean_uint16_shift_right(v___x_2218_, v___x_2233_);
v___x_2235_ = 1;
v___x_2236_ = lean_uint16_land(v___x_2234_, v___x_2235_);
v___x_2237_ = 0;
v___x_2238_ = lean_uint16_dec_eq(v___x_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
return v___y_2219_;
}
else
{
uint8_t v___x_2239_; uint8_t v___x_2240_; uint8_t v___x_2241_; uint8_t v___x_2242_; uint8_t v___x_2243_; uint8_t v___x_2244_; uint8_t v___x_2245_; uint8_t v___x_2246_; uint8_t v___x_2247_; uint8_t v___x_2248_; uint16_t v___x_2249_; uint16_t v___x_2250_; uint16_t v___x_2251_; uint16_t v___x_2252_; uint8_t v___x_2253_; 
v___x_2239_ = 253;
v___x_2240_ = lean_uint8_land(v_s_2217_, v___x_2239_);
v___x_2241_ = 1;
v___x_2242_ = lean_uint8_shift_left(v___x_2225_, v___x_2241_);
v___x_2243_ = lean_uint8_lor(v___x_2240_, v___x_2242_);
v___x_2244_ = 247;
v___x_2245_ = lean_uint8_land(v___x_2243_, v___x_2244_);
v___x_2246_ = 3;
v___x_2247_ = lean_uint8_shift_left(v___x_2229_, v___x_2246_);
v___x_2248_ = lean_uint8_lor(v___x_2245_, v___x_2247_);
v___x_2249_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2220_);
v___x_2250_ = lean_uint8_to_uint16(v___x_2248_);
v___x_2251_ = lean_uint16_shift_right(v___x_2249_, v___x_2250_);
v___x_2252_ = lean_uint16_land(v___x_2251_, v___x_2235_);
v___x_2253_ = lean_uint16_dec_eq(v___x_2252_, v___x_2237_);
if (v___x_2253_ == 0)
{
return v___y_2219_;
}
else
{
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0___boxed(lean_object* v_s_2254_, lean_object* v___x_2255_, lean_object* v___y_2256_, lean_object* v_b_2257_, lean_object* v_isMidFull_2258_, lean_object* v_isMidInitial_2259_){
_start:
{
uint8_t v_s_boxed_2260_; uint16_t v___x_2171__boxed_2261_; uint8_t v___y_2172__boxed_2262_; uint8_t v_isMidFull_boxed_2263_; uint8_t v_isMidInitial_boxed_2264_; uint8_t v_res_2265_; lean_object* v_r_2266_; 
v_s_boxed_2260_ = lean_unbox(v_s_2254_);
v___x_2171__boxed_2261_ = lean_unbox(v___x_2255_);
v___y_2172__boxed_2262_ = lean_unbox(v___y_2256_);
v_isMidFull_boxed_2263_ = lean_unbox(v_isMidFull_2258_);
v_isMidInitial_boxed_2264_ = lean_unbox(v_isMidInitial_2259_);
v_res_2265_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_boxed_2260_, v___x_2171__boxed_2261_, v___y_2172__boxed_2262_, v_b_2257_, v_isMidFull_boxed_2263_, v_isMidInitial_boxed_2264_);
lean_dec(v_b_2257_);
v_r_2266_ = lean_box(v_res_2265_);
return v_r_2266_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(uint16_t v___x_2267_, uint8_t v___y_2268_, lean_object* v_b_2269_, lean_object* v_x_2270_, uint16_t v_x_2271_){
_start:
{
lean_object* v_zero_2272_; uint8_t v_isZero_2273_; 
v_zero_2272_ = lean_unsigned_to_nat(0u);
v_isZero_2273_ = lean_nat_dec_eq(v_x_2270_, v_zero_2272_);
if (v_isZero_2273_ == 1)
{
lean_dec(v_x_2270_);
return v_x_2271_;
}
else
{
lean_object* v_one_2274_; lean_object* v_n_2275_; uint8_t v_s_2282_; uint8_t v___x_2283_; 
v_one_2274_ = lean_unsigned_to_nat(1u);
v_n_2275_ = lean_nat_sub(v_x_2270_, v_one_2274_);
lean_dec(v_x_2270_);
v_s_2282_ = lean_uint8_of_nat(v_n_2275_);
v___x_2283_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2282_, v___x_2267_, v___y_2268_, v_b_2269_, v_isZero_2273_, v_isZero_2273_);
if (v___x_2283_ == 0)
{
uint8_t v___x_2284_; uint8_t v___x_2285_; 
v___x_2284_ = 1;
v___x_2285_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2282_, v___x_2267_, v___y_2268_, v_b_2269_, v___x_2283_, v___x_2284_);
if (v___x_2285_ == 0)
{
uint8_t v___x_2286_; 
v___x_2286_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2282_, v___x_2267_, v___y_2268_, v_b_2269_, v___x_2284_, v___x_2285_);
if (v___x_2286_ == 0)
{
uint8_t v___x_2287_; 
v___x_2287_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___lam__0(v_s_2282_, v___x_2267_, v___y_2268_, v_b_2269_, v___x_2284_, v___x_2284_);
if (v___x_2287_ == 0)
{
v_x_2270_ = v_n_2275_;
goto _start;
}
else
{
goto v___jp_2276_;
}
}
else
{
goto v___jp_2276_;
}
}
else
{
goto v___jp_2276_;
}
}
else
{
goto v___jp_2276_;
}
v___jp_2276_:
{
uint16_t v___x_2277_; uint16_t v___x_2278_; uint16_t v___x_2279_; uint16_t v___x_2280_; 
v___x_2277_ = 1;
v___x_2278_ = lean_uint16_of_nat(v_n_2275_);
v___x_2279_ = lean_uint16_shift_left(v___x_2277_, v___x_2278_);
v___x_2280_ = lean_uint16_lor(v_x_2271_, v___x_2279_);
v_x_2270_ = v_n_2275_;
v_x_2271_ = v___x_2280_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg___boxed(lean_object* v___x_2289_, lean_object* v___y_2290_, lean_object* v_b_2291_, lean_object* v_x_2292_, lean_object* v_x_2293_){
_start:
{
uint16_t v___x_2239__boxed_2294_; uint8_t v___y_2240__boxed_2295_; uint16_t v_x_2242__boxed_2296_; uint16_t v_res_2297_; lean_object* v_r_2298_; 
v___x_2239__boxed_2294_ = lean_unbox(v___x_2289_);
v___y_2240__boxed_2295_ = lean_unbox(v___y_2290_);
v_x_2242__boxed_2296_ = lean_unbox(v_x_2293_);
v_res_2297_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2239__boxed_2294_, v___y_2240__boxed_2295_, v_b_2291_, v_x_2292_, v_x_2242__boxed_2296_);
lean_dec(v_b_2291_);
v_r_2298_ = lean_box(v_res_2297_);
return v_r_2298_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(uint16_t v___x_2299_, uint8_t v___y_2300_, lean_object* v_b_2301_){
_start:
{
lean_object* v___x_2302_; uint16_t v___x_2303_; uint16_t v___x_2304_; 
v___x_2302_ = lean_unsigned_to_nat(16u);
v___x_2303_ = 0;
v___x_2304_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2299_, v___y_2300_, v_b_2301_, v___x_2302_, v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg___boxed(lean_object* v___x_2305_, lean_object* v___y_2306_, lean_object* v_b_2307_){
_start:
{
uint16_t v___x_2277__boxed_2308_; uint8_t v___y_2278__boxed_2309_; uint16_t v_res_2310_; lean_object* v_r_2311_; 
v___x_2277__boxed_2308_ = lean_unbox(v___x_2305_);
v___y_2278__boxed_2309_ = lean_unbox(v___y_2306_);
v_res_2310_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2277__boxed_2308_, v___y_2278__boxed_2309_, v_b_2307_);
lean_dec(v_b_2307_);
v_r_2311_ = lean_box(v_res_2310_);
return v_r_2311_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(uint8_t v_s_2312_, uint16_t v___x_2313_, uint16_t v___x_2314_, lean_object* v_b_2315_, uint8_t v___x_2316_, uint8_t v_isMidFull_2317_, uint8_t v_isMidInitial_2318_){
_start:
{
uint8_t v___x_2319_; uint8_t v___x_2320_; uint8_t v___x_2321_; uint8_t v___x_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; uint8_t v___x_2326_; uint8_t v___x_2327_; uint8_t v___x_2328_; uint16_t v___x_2329_; uint16_t v___x_2330_; uint16_t v___x_2331_; uint16_t v___x_2332_; uint8_t v___x_2333_; 
v___x_2319_ = 254;
v___x_2320_ = lean_uint8_land(v_s_2312_, v___x_2319_);
v___x_2321_ = lean_bool_to_uint8(v_isMidFull_2317_);
v___x_2322_ = lean_uint8_lor(v___x_2320_, v___x_2321_);
v___x_2323_ = 251;
v___x_2324_ = lean_uint8_land(v___x_2322_, v___x_2323_);
v___x_2325_ = lean_bool_to_uint8(v_isMidInitial_2318_);
v___x_2326_ = 2;
v___x_2327_ = lean_uint8_shift_left(v___x_2325_, v___x_2326_);
v___x_2328_ = lean_uint8_lor(v___x_2324_, v___x_2327_);
v___x_2329_ = lean_uint8_to_uint16(v___x_2328_);
v___x_2330_ = lean_uint16_shift_right(v___x_2313_, v___x_2329_);
v___x_2331_ = 1;
v___x_2332_ = lean_uint16_land(v___x_2330_, v___x_2331_);
v___x_2333_ = lean_uint16_dec_eq(v___x_2332_, v___x_2314_);
if (v___x_2333_ == 0)
{
uint8_t v___x_2334_; uint8_t v___x_2335_; uint8_t v___x_2336_; uint8_t v___x_2337_; uint8_t v___x_2338_; uint8_t v___x_2339_; uint8_t v___x_2340_; uint8_t v___x_2341_; uint8_t v___x_2342_; uint8_t v___x_2343_; uint16_t v___x_2344_; uint16_t v___x_2345_; uint16_t v___x_2346_; uint16_t v___x_2347_; uint8_t v___x_2348_; 
v___x_2334_ = 253;
v___x_2335_ = lean_uint8_land(v_s_2312_, v___x_2334_);
v___x_2336_ = 1;
v___x_2337_ = lean_uint8_shift_left(v___x_2321_, v___x_2336_);
v___x_2338_ = lean_uint8_lor(v___x_2335_, v___x_2337_);
v___x_2339_ = 247;
v___x_2340_ = lean_uint8_land(v___x_2338_, v___x_2339_);
v___x_2341_ = 3;
v___x_2342_ = lean_uint8_shift_left(v___x_2325_, v___x_2341_);
v___x_2343_ = lean_uint8_lor(v___x_2340_, v___x_2342_);
v___x_2344_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2315_);
v___x_2345_ = lean_uint8_to_uint16(v___x_2343_);
v___x_2346_ = lean_uint16_shift_right(v___x_2344_, v___x_2345_);
v___x_2347_ = lean_uint16_land(v___x_2346_, v___x_2331_);
v___x_2348_ = lean_uint16_dec_eq(v___x_2347_, v___x_2314_);
if (v___x_2348_ == 0)
{
uint8_t v___x_2349_; 
v___x_2349_ = 1;
return v___x_2349_;
}
else
{
return v___x_2316_;
}
}
else
{
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0___boxed(lean_object* v_s_2350_, lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v_b_2353_, lean_object* v___x_2354_, lean_object* v_isMidFull_2355_, lean_object* v_isMidInitial_2356_){
_start:
{
uint8_t v_s_boxed_2357_; uint16_t v___x_2289__boxed_2358_; uint16_t v___x_2290__boxed_2359_; uint8_t v___x_2291__boxed_2360_; uint8_t v_isMidFull_boxed_2361_; uint8_t v_isMidInitial_boxed_2362_; uint8_t v_res_2363_; lean_object* v_r_2364_; 
v_s_boxed_2357_ = lean_unbox(v_s_2350_);
v___x_2289__boxed_2358_ = lean_unbox(v___x_2351_);
v___x_2290__boxed_2359_ = lean_unbox(v___x_2352_);
v___x_2291__boxed_2360_ = lean_unbox(v___x_2354_);
v_isMidFull_boxed_2361_ = lean_unbox(v_isMidFull_2355_);
v_isMidInitial_boxed_2362_ = lean_unbox(v_isMidInitial_2356_);
v_res_2363_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_boxed_2357_, v___x_2289__boxed_2358_, v___x_2290__boxed_2359_, v_b_2353_, v___x_2291__boxed_2360_, v_isMidFull_boxed_2361_, v_isMidInitial_boxed_2362_);
lean_dec(v_b_2353_);
v_r_2364_ = lean_box(v_res_2363_);
return v_r_2364_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(uint16_t v___x_2365_, lean_object* v_b_2366_, uint16_t v___x_2367_, lean_object* v_x_2368_, uint16_t v_x_2369_){
_start:
{
lean_object* v_zero_2370_; uint8_t v_isZero_2371_; 
v_zero_2370_ = lean_unsigned_to_nat(0u);
v_isZero_2371_ = lean_nat_dec_eq(v_x_2368_, v_zero_2370_);
if (v_isZero_2371_ == 1)
{
lean_dec(v_x_2368_);
return v_x_2369_;
}
else
{
uint16_t v___x_2372_; uint8_t v___x_2373_; lean_object* v_one_2374_; lean_object* v_n_2375_; uint8_t v_s_2382_; uint8_t v___x_2383_; 
v___x_2372_ = 0;
v___x_2373_ = lean_uint16_dec_eq(v___x_2367_, v___x_2372_);
v_one_2374_ = lean_unsigned_to_nat(1u);
v_n_2375_ = lean_nat_sub(v_x_2368_, v_one_2374_);
lean_dec(v_x_2368_);
v_s_2382_ = lean_uint8_of_nat(v_n_2375_);
v___x_2383_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2382_, v___x_2365_, v___x_2372_, v_b_2366_, v___x_2373_, v_isZero_2371_, v_isZero_2371_);
if (v___x_2383_ == 0)
{
uint8_t v___x_2384_; uint8_t v___x_2385_; 
v___x_2384_ = 1;
v___x_2385_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2382_, v___x_2365_, v___x_2372_, v_b_2366_, v___x_2373_, v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
uint8_t v___x_2386_; 
v___x_2386_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2382_, v___x_2365_, v___x_2372_, v_b_2366_, v___x_2373_, v___x_2384_, v___x_2385_);
if (v___x_2386_ == 0)
{
uint8_t v___x_2387_; 
v___x_2387_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___lam__0(v_s_2382_, v___x_2365_, v___x_2372_, v_b_2366_, v___x_2373_, v___x_2384_, v___x_2384_);
if (v___x_2387_ == 0)
{
v_x_2368_ = v_n_2375_;
goto _start;
}
else
{
goto v___jp_2376_;
}
}
else
{
goto v___jp_2376_;
}
}
else
{
goto v___jp_2376_;
}
}
else
{
goto v___jp_2376_;
}
v___jp_2376_:
{
uint16_t v___x_2377_; uint16_t v___x_2378_; uint16_t v___x_2379_; uint16_t v___x_2380_; 
v___x_2377_ = 1;
v___x_2378_ = lean_uint16_of_nat(v_n_2375_);
v___x_2379_ = lean_uint16_shift_left(v___x_2377_, v___x_2378_);
v___x_2380_ = lean_uint16_lor(v_x_2369_, v___x_2379_);
v_x_2368_ = v_n_2375_;
v_x_2369_ = v___x_2380_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg___boxed(lean_object* v___x_2389_, lean_object* v_b_2390_, lean_object* v___x_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
uint16_t v___x_2360__boxed_2394_; uint16_t v___x_2361__boxed_2395_; uint16_t v_x_2363__boxed_2396_; uint16_t v_res_2397_; lean_object* v_r_2398_; 
v___x_2360__boxed_2394_ = lean_unbox(v___x_2389_);
v___x_2361__boxed_2395_ = lean_unbox(v___x_2391_);
v_x_2363__boxed_2396_ = lean_unbox(v_x_2393_);
v_res_2397_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(v___x_2360__boxed_2394_, v_b_2390_, v___x_2361__boxed_2395_, v_x_2392_, v_x_2363__boxed_2396_);
lean_dec(v_b_2390_);
v_r_2398_ = lean_box(v_res_2397_);
return v_r_2398_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(uint16_t v___x_2399_, lean_object* v_b_2400_, uint16_t v___x_2401_){
_start:
{
lean_object* v___x_2402_; uint16_t v___x_2403_; uint16_t v___x_2404_; 
v___x_2402_ = lean_unsigned_to_nat(16u);
v___x_2403_ = 0;
v___x_2404_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(v___x_2399_, v_b_2400_, v___x_2401_, v___x_2402_, v___x_2403_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg___boxed(lean_object* v___x_2405_, lean_object* v_b_2406_, lean_object* v___x_2407_){
_start:
{
uint16_t v___x_2402__boxed_2408_; uint16_t v___x_2403__boxed_2409_; uint16_t v_res_2410_; lean_object* v_r_2411_; 
v___x_2402__boxed_2408_ = lean_unbox(v___x_2405_);
v___x_2403__boxed_2409_ = lean_unbox(v___x_2407_);
v_res_2410_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(v___x_2402__boxed_2408_, v_b_2406_, v___x_2403__boxed_2409_);
lean_dec(v_b_2406_);
v_r_2411_ = lean_box(v_res_2410_);
return v_r_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object* v_a_2412_, lean_object* v_b_2413_){
_start:
{
uint8_t v___y_2415_; uint8_t v___y_2416_; uint16_t v___y_2417_; lean_object* v___y_2418_; uint8_t v___y_2419_; lean_object* v___f_2429_; uint16_t v___y_2431_; uint16_t v___x_2448_; uint16_t v___x_2449_; uint8_t v___x_2450_; 
v___f_2429_ = ((lean_object*)(l_Lean_Fmt_instHAddTagIdNat___closed__0));
v___x_2448_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_a_2412_);
v___x_2449_ = 65535;
v___x_2450_ = lean_uint16_dec_eq(v___x_2448_, v___x_2449_);
if (v___x_2450_ == 0)
{
uint16_t v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_b_2413_);
v___x_2452_ = lean_uint16_dec_eq(v___x_2451_, v___x_2449_);
if (v___x_2452_ == 0)
{
uint16_t v___x_2453_; uint16_t v___x_2454_; 
v___x_2453_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2448_, v___x_2452_, v_b_2413_);
v___x_2454_ = lean_uint16_complement(v___x_2453_);
v___y_2431_ = v___x_2454_;
goto v___jp_2430_;
}
else
{
v___y_2431_ = v___x_2449_;
goto v___jp_2430_;
}
}
else
{
v___y_2431_ = v___x_2449_;
goto v___jp_2430_;
}
v___jp_2414_:
{
uint16_t v___x_2420_; uint16_t v___x_2421_; uint8_t v___x_2422_; 
v___x_2420_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_a_2412_);
v___x_2421_ = 0;
v___x_2422_ = lean_uint16_dec_eq(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
uint16_t v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_b_2413_);
v___x_2424_ = lean_uint16_dec_eq(v___x_2423_, v___x_2421_);
if (v___x_2424_ == 0)
{
uint16_t v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(v___x_2420_, v_b_2413_, v___x_2423_);
v___x_2426_ = lean_alloc_ctor(15, 3, 7);
lean_ctor_set(v___x_2426_, 0, v___y_2418_);
lean_ctor_set(v___x_2426_, 1, v_a_2412_);
lean_ctor_set(v___x_2426_, 2, v_b_2413_);
lean_ctor_set_uint16(v___x_2426_, sizeof(void*)*3, v___y_2417_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*3 + 4, v___y_2415_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*3 + 5, v___y_2416_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*3 + 6, v___y_2419_);
lean_ctor_set_uint16(v___x_2426_, sizeof(void*)*3 + 2, v___x_2425_);
return v___x_2426_;
}
else
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_alloc_ctor(15, 3, 7);
lean_ctor_set(v___x_2427_, 0, v___y_2418_);
lean_ctor_set(v___x_2427_, 1, v_a_2412_);
lean_ctor_set(v___x_2427_, 2, v_b_2413_);
lean_ctor_set_uint16(v___x_2427_, sizeof(void*)*3, v___y_2417_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 4, v___y_2415_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 5, v___y_2416_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 6, v___y_2419_);
lean_ctor_set_uint16(v___x_2427_, sizeof(void*)*3 + 2, v___x_2421_);
return v___x_2427_;
}
}
else
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_ctor(15, 3, 7);
lean_ctor_set(v___x_2428_, 0, v___y_2418_);
lean_ctor_set(v___x_2428_, 1, v_a_2412_);
lean_ctor_set(v___x_2428_, 2, v_b_2413_);
lean_ctor_set_uint16(v___x_2428_, sizeof(void*)*3, v___y_2417_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*3 + 4, v___y_2415_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*3 + 5, v___y_2416_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*3 + 6, v___y_2419_);
lean_ctor_set_uint16(v___x_2428_, sizeof(void*)*3 + 2, v___x_2421_);
return v___x_2428_;
}
}
v___jp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; uint8_t v___x_2436_; uint8_t v___x_2437_; uint8_t v___x_2438_; uint8_t v___x_2439_; uint8_t v___x_2440_; 
v___x_2432_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_2412_);
v___x_2433_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_2413_);
v___x_2434_ = l_Option_merge___redArg(v___f_2429_, v___x_2432_, v___x_2433_);
v___x_2435_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_2412_);
v___x_2436_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_2413_);
v___x_2437_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_2435_, v___x_2436_);
v___x_2438_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_2412_);
v___x_2439_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_2413_);
v___x_2440_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_2438_, v___x_2439_);
if (v___x_2435_ == 0)
{
uint8_t v___x_2441_; 
v___x_2441_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_2413_);
v___y_2415_ = v___x_2437_;
v___y_2416_ = v___x_2440_;
v___y_2417_ = v___y_2431_;
v___y_2418_ = v___x_2434_;
v___y_2419_ = v___x_2441_;
goto v___jp_2414_;
}
else
{
if (v___x_2436_ == 0)
{
uint8_t v___x_2442_; 
v___x_2442_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_2412_);
v___y_2415_ = v___x_2437_;
v___y_2416_ = v___x_2440_;
v___y_2417_ = v___y_2431_;
v___y_2418_ = v___x_2434_;
v___y_2419_ = v___x_2442_;
goto v___jp_2414_;
}
else
{
uint8_t v___x_2443_; uint8_t v___x_2444_; uint8_t v___x_2445_; uint8_t v___x_2446_; uint8_t v___x_2447_; 
v___x_2443_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_2412_);
v___x_2444_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_2413_);
v___x_2445_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_2443_, v___x_2444_);
v___x_2446_ = 2;
v___x_2447_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_2445_, v___x_2446_);
v___y_2415_ = v___x_2437_;
v___y_2416_ = v___x_2440_;
v___y_2417_ = v___y_2431_;
v___y_2418_ = v___x_2434_;
v___y_2419_ = v___x_2447_;
goto v___jp_2414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object* v_00_u03c4_2455_, lean_object* v_a_2456_, lean_object* v_b_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_Fmt_Doc_append___override___redArg(v_a_2456_, v_b_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15(uint16_t v___x_2459_, lean_object* v_00_u03c4_2460_, lean_object* v_b_2461_, uint16_t v___x_2462_){
_start:
{
uint16_t v___x_2463_; 
v___x_2463_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___redArg(v___x_2459_, v_b_2461_, v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15___boxed(lean_object* v___x_2464_, lean_object* v_00_u03c4_2465_, lean_object* v_b_2466_, lean_object* v___x_2467_){
_start:
{
uint16_t v___x_2499__boxed_2468_; uint16_t v___x_2500__boxed_2469_; uint16_t v_res_2470_; lean_object* v_r_2471_; 
v___x_2499__boxed_2468_ = lean_unbox(v___x_2464_);
v___x_2500__boxed_2469_ = lean_unbox(v___x_2467_);
v_res_2470_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15(v___x_2499__boxed_2468_, v_00_u03c4_2465_, v_b_2466_, v___x_2500__boxed_2469_);
lean_dec(v_b_2466_);
v_r_2471_ = lean_box(v_res_2470_);
return v_r_2471_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(uint16_t v___x_2472_, uint8_t v___y_2473_, lean_object* v_00_u03c4_2474_, lean_object* v_b_2475_){
_start:
{
uint16_t v___x_2476_; 
v___x_2476_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___redArg(v___x_2472_, v___y_2473_, v_b_2475_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16___boxed(lean_object* v___x_2477_, lean_object* v___y_2478_, lean_object* v_00_u03c4_2479_, lean_object* v_b_2480_){
_start:
{
uint16_t v___x_2507__boxed_2481_; uint8_t v___y_2508__boxed_2482_; uint16_t v_res_2483_; lean_object* v_r_2484_; 
v___x_2507__boxed_2481_ = lean_unbox(v___x_2477_);
v___y_2508__boxed_2482_ = lean_unbox(v___y_2478_);
v_res_2483_ = l_Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16(v___x_2507__boxed_2481_, v___y_2508__boxed_2482_, v_00_u03c4_2479_, v_b_2480_);
lean_dec(v_b_2480_);
v_r_2484_ = lean_box(v_res_2483_);
return v_r_2484_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21(uint16_t v___x_2485_, lean_object* v_00_u03c4_2486_, lean_object* v_b_2487_, uint16_t v___x_2488_, lean_object* v_x_2489_, uint16_t v_x_2490_){
_start:
{
uint16_t v___x_2491_; 
v___x_2491_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___redArg(v___x_2485_, v_b_2487_, v___x_2488_, v_x_2489_, v_x_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21___boxed(lean_object* v___x_2492_, lean_object* v_00_u03c4_2493_, lean_object* v_b_2494_, lean_object* v___x_2495_, lean_object* v_x_2496_, lean_object* v_x_2497_){
_start:
{
uint16_t v___x_2515__boxed_2498_; uint16_t v___x_2516__boxed_2499_; uint16_t v_x_2518__boxed_2500_; uint16_t v_res_2501_; lean_object* v_r_2502_; 
v___x_2515__boxed_2498_ = lean_unbox(v___x_2492_);
v___x_2516__boxed_2499_ = lean_unbox(v___x_2495_);
v_x_2518__boxed_2500_ = lean_unbox(v_x_2497_);
v_res_2501_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__15_spec__21(v___x_2515__boxed_2498_, v_00_u03c4_2493_, v_b_2494_, v___x_2516__boxed_2499_, v_x_2496_, v_x_2518__boxed_2500_);
lean_dec(v_b_2494_);
v_r_2502_ = lean_box(v_res_2501_);
return v_r_2502_;
}
}
LEAN_EXPORT uint16_t l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(uint16_t v___x_2503_, uint8_t v___y_2504_, lean_object* v_00_u03c4_2505_, lean_object* v_b_2506_, lean_object* v_x_2507_, uint16_t v_x_2508_){
_start:
{
uint16_t v___x_2509_; 
v___x_2509_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___redArg(v___x_2503_, v___y_2504_, v_b_2506_, v_x_2507_, v_x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23___boxed(lean_object* v___x_2510_, lean_object* v___y_2511_, lean_object* v_00_u03c4_2512_, lean_object* v_b_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
uint16_t v___x_2529__boxed_2516_; uint8_t v___y_2530__boxed_2517_; uint16_t v_x_2532__boxed_2518_; uint16_t v_res_2519_; lean_object* v_r_2520_; 
v___x_2529__boxed_2516_ = lean_unbox(v___x_2510_);
v___y_2530__boxed_2517_ = lean_unbox(v___y_2511_);
v_x_2532__boxed_2518_ = lean_unbox(v_x_2515_);
v_res_2519_ = l_Lean_Fmt_FullnessStateSet_ofPredBelow___at___00Lean_Fmt_FullnessStateSet_anySplit___at___00Lean_Fmt_Doc_append___override_spec__16_spec__23(v___x_2529__boxed_2516_, v___y_2530__boxed_2517_, v_00_u03c4_2512_, v_b_2513_, v_x_2514_, v_x_2532__boxed_2518_);
lean_dec(v_b_2513_);
v_r_2520_ = lean_box(v_res_2519_);
return v_r_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg(){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_box(0);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default___redArg___boxed(lean_object* v___dummy_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Fmt_instInhabitedDoc_default___redArg();
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object* v_00_u03c4_2525_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_box(0);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg(){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_box(0);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc___redArg___boxed(lean_object* v___dummy_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Fmt_instInhabitedDoc___redArg();
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc(lean_object* v_a_2531_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_box(0);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_unsigned_to_nat(2u);
v___x_2537_ = lean_nat_to_int(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_unsigned_to_nat(1u);
v___x_2539_ = lean_nat_to_int(v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg(lean_object* v_inst_2636_, lean_object* v_x_2637_, lean_object* v_prec_2638_){
_start:
{
lean_object* v___y_2640_; 
switch(lean_obj_tag(v_x_2637_))
{
case 0:
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
lean_dec_ref(v_inst_2636_);
v___x_2646_ = lean_unsigned_to_nat(1024u);
v___x_2647_ = lean_nat_dec_le(v___x_2646_, v_prec_2638_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2640_ = v___x_2648_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2649_; 
v___x_2649_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2640_ = v___x_2649_;
goto v___jp_2639_;
}
}
case 1:
{
lean_object* v_f_2650_; lean_object* v___y_2652_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
lean_dec_ref(v_inst_2636_);
v_f_2650_ = lean_ctor_get(v_x_2637_, 1);
lean_inc_ref(v_f_2650_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2661_ = lean_unsigned_to_nat(1024u);
v___x_2662_ = lean_nat_dec_le(v___x_2661_, v_prec_2638_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2652_ = v___x_2663_;
goto v___jp_2651_;
}
else
{
lean_object* v___x_2664_; 
v___x_2664_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2652_ = v___x_2664_;
goto v___jp_2651_;
}
v___jp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2653_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__6));
v___x_2654_ = l_String_quote(v_f_2650_);
v___x_2655_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2653_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
lean_inc(v___y_2652_);
v___x_2657_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2652_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = 0;
v___x_2659_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set_uint8(v___x_2659_, sizeof(void*)*1, v___x_2658_);
v___x_2660_ = l_Repr_addAppParen(v___x_2659_, v_prec_2638_);
return v___x_2660_;
}
}
case 2:
{
lean_object* v_s_2665_; lean_object* v___y_2667_; lean_object* v___x_2676_; uint8_t v___x_2677_; 
lean_dec_ref(v_inst_2636_);
v_s_2665_ = lean_ctor_get(v_x_2637_, 1);
lean_inc_ref(v_s_2665_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2676_ = lean_unsigned_to_nat(1024u);
v___x_2677_ = lean_nat_dec_le(v___x_2676_, v_prec_2638_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2667_ = v___x_2678_;
goto v___jp_2666_;
}
else
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2667_ = v___x_2679_;
goto v___jp_2666_;
}
v___jp_2666_:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2668_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__9));
v___x_2669_ = l_String_quote(v_s_2665_);
v___x_2670_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
v___x_2671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2668_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
lean_inc(v___y_2667_);
v___x_2672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___y_2667_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = 0;
v___x_2674_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*1, v___x_2673_);
v___x_2675_ = l_Repr_addAppParen(v___x_2674_, v_prec_2638_);
return v___x_2675_;
}
}
case 3:
{
lean_object* v_id_2680_; lean_object* v_d_2681_; lean_object* v___x_2682_; lean_object* v___y_2684_; uint8_t v___x_2697_; 
v_id_2680_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_id_2680_);
v_d_2681_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_d_2681_);
lean_dec_ref_known(v_x_2637_, 3);
v___x_2682_ = lean_unsigned_to_nat(1024u);
v___x_2697_ = lean_nat_dec_le(v___x_2682_, v_prec_2638_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
v___x_2698_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2684_ = v___x_2698_;
goto v___jp_2683_;
}
else
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2684_ = v___x_2699_;
goto v___jp_2683_;
}
v___jp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2685_ = lean_box(1);
v___x_2686_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__12));
v___x_2687_ = l_Nat_reprFast(v_id_2680_);
v___x_2688_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
v___x_2689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2686_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v___x_2685_);
v___x_2691_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2681_, v___x_2682_);
v___x_2692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
lean_inc(v___y_2684_);
v___x_2693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___y_2684_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = 0;
v___x_2695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set_uint8(v___x_2695_, sizeof(void*)*1, v___x_2694_);
v___x_2696_ = l_Repr_addAppParen(v___x_2695_, v_prec_2638_);
return v___x_2696_;
}
}
case 4:
{
lean_object* v_d_2700_; lean_object* v___x_2701_; lean_object* v___y_2703_; uint8_t v___x_2711_; 
v_d_2700_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_d_2700_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2701_ = lean_unsigned_to_nat(1024u);
v___x_2711_ = lean_nat_dec_le(v___x_2701_, v_prec_2638_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2703_ = v___x_2712_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2703_ = v___x_2713_;
goto v___jp_2702_;
}
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2704_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__15));
v___x_2705_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2700_, v___x_2701_);
v___x_2706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_inc(v___y_2703_);
v___x_2707_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___y_2703_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = 0;
v___x_2709_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*1, v___x_2708_);
v___x_2710_ = l_Repr_addAppParen(v___x_2709_, v_prec_2638_);
return v___x_2710_;
}
}
case 5:
{
lean_object* v_d_2714_; lean_object* v___x_2715_; lean_object* v___y_2717_; uint8_t v___x_2725_; 
v_d_2714_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_d_2714_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2715_ = lean_unsigned_to_nat(1024u);
v___x_2725_ = lean_nat_dec_le(v___x_2715_, v_prec_2638_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2717_ = v___x_2726_;
goto v___jp_2716_;
}
else
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2717_ = v___x_2727_;
goto v___jp_2716_;
}
v___jp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2718_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__18));
v___x_2719_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2714_, v___x_2715_);
v___x_2720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
lean_inc(v___y_2717_);
v___x_2721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___y_2717_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = 0;
v___x_2723_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set_uint8(v___x_2723_, sizeof(void*)*1, v___x_2722_);
v___x_2724_ = l_Repr_addAppParen(v___x_2723_, v_prec_2638_);
return v___x_2724_;
}
}
case 6:
{
lean_object* v_n_2728_; uint8_t v_isCumulative_2729_; lean_object* v_d_2730_; lean_object* v___x_2731_; lean_object* v___y_2733_; uint8_t v___x_2749_; 
v_n_2728_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_n_2728_);
v_isCumulative_2729_ = lean_ctor_get_uint8(v_x_2637_, sizeof(void*)*3 + 7);
v_d_2730_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_d_2730_);
lean_dec_ref_known(v_x_2637_, 3);
v___x_2731_ = lean_unsigned_to_nat(1024u);
v___x_2749_ = lean_nat_dec_le(v___x_2731_, v_prec_2638_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2733_ = v___x_2750_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2733_ = v___x_2751_;
goto v___jp_2732_;
}
v___jp_2732_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2734_ = lean_box(1);
v___x_2735_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__21));
v___x_2736_ = l_Nat_reprFast(v_n_2728_);
v___x_2737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
v___x_2738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2735_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v___x_2734_);
v___x_2740_ = l_Bool_repr___redArg(v_isCumulative_2729_);
v___x_2741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
lean_ctor_set(v___x_2742_, 1, v___x_2734_);
v___x_2743_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2730_, v___x_2731_);
v___x_2744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_inc(v___y_2733_);
v___x_2745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___y_2733_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = 0;
v___x_2747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*1, v___x_2746_);
v___x_2748_ = l_Repr_addAppParen(v___x_2747_, v_prec_2638_);
return v___x_2748_;
}
}
case 7:
{
lean_object* v_d_2752_; lean_object* v___x_2753_; lean_object* v___y_2755_; uint8_t v___x_2763_; 
v_d_2752_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_d_2752_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2753_ = lean_unsigned_to_nat(1024u);
v___x_2763_ = lean_nat_dec_le(v___x_2753_, v_prec_2638_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2755_ = v___x_2764_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2755_ = v___x_2765_;
goto v___jp_2754_;
}
v___jp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2756_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__24));
v___x_2757_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2752_, v___x_2753_);
v___x_2758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_inc(v___y_2755_);
v___x_2759_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___y_2755_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = 0;
v___x_2761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*1, v___x_2760_);
v___x_2762_ = l_Repr_addAppParen(v___x_2761_, v_prec_2638_);
return v___x_2762_;
}
}
case 8:
{
uint8_t v_onlyNonCumulative_2766_; lean_object* v_d_2767_; lean_object* v___x_2768_; lean_object* v___y_2770_; uint8_t v___x_2782_; 
v_onlyNonCumulative_2766_ = lean_ctor_get_uint8(v_x_2637_, sizeof(void*)*2 + 7);
v_d_2767_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_d_2767_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2768_ = lean_unsigned_to_nat(1024u);
v___x_2782_ = lean_nat_dec_le(v___x_2768_, v_prec_2638_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2770_ = v___x_2783_;
goto v___jp_2769_;
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2770_ = v___x_2784_;
goto v___jp_2769_;
}
v___jp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2771_ = lean_box(1);
v___x_2772_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__27));
v___x_2773_ = l_Bool_repr___redArg(v_onlyNonCumulative_2766_);
v___x_2774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set(v___x_2774_, 1, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v___x_2771_);
v___x_2776_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2767_, v___x_2768_);
v___x_2777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
lean_inc(v___y_2770_);
v___x_2778_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___y_2770_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = 0;
v___x_2780_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set_uint8(v___x_2780_, sizeof(void*)*1, v___x_2779_);
v___x_2781_ = l_Repr_addAppParen(v___x_2780_, v_prec_2638_);
return v___x_2781_;
}
}
case 9:
{
lean_object* v_d_2785_; lean_object* v___x_2786_; lean_object* v___y_2788_; uint8_t v___x_2796_; 
v_d_2785_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_d_2785_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2786_ = lean_unsigned_to_nat(1024u);
v___x_2796_ = lean_nat_dec_le(v___x_2786_, v_prec_2638_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2788_ = v___x_2797_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2788_ = v___x_2798_;
goto v___jp_2787_;
}
v___jp_2787_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2789_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__30));
v___x_2790_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2785_, v___x_2786_);
v___x_2791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
lean_inc(v___y_2788_);
v___x_2792_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___y_2788_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = 0;
v___x_2794_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set_uint8(v___x_2794_, sizeof(void*)*1, v___x_2793_);
v___x_2795_ = l_Repr_addAppParen(v___x_2794_, v_prec_2638_);
return v___x_2795_;
}
}
case 10:
{
lean_object* v_d_2799_; lean_object* v___x_2800_; lean_object* v___y_2802_; uint8_t v___x_2810_; 
v_d_2799_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_d_2799_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2800_ = lean_unsigned_to_nat(1024u);
v___x_2810_ = lean_nat_dec_le(v___x_2800_, v_prec_2638_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2802_ = v___x_2811_;
goto v___jp_2801_;
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2802_ = v___x_2812_;
goto v___jp_2801_;
}
v___jp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2803_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__33));
v___x_2804_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2799_, v___x_2800_);
v___x_2805_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2803_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
lean_inc(v___y_2802_);
v___x_2806_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___y_2802_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = 0;
v___x_2808_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set_uint8(v___x_2808_, sizeof(void*)*1, v___x_2807_);
v___x_2809_ = l_Repr_addAppParen(v___x_2808_, v_prec_2638_);
return v___x_2809_;
}
}
case 11:
{
lean_object* v_d_2813_; lean_object* v___x_2814_; lean_object* v___y_2816_; uint8_t v___x_2824_; 
v_d_2813_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_d_2813_);
lean_dec_ref_known(v_x_2637_, 2);
v___x_2814_ = lean_unsigned_to_nat(1024u);
v___x_2824_ = lean_nat_dec_le(v___x_2814_, v_prec_2638_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2816_ = v___x_2825_;
goto v___jp_2815_;
}
else
{
lean_object* v___x_2826_; 
v___x_2826_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2816_ = v___x_2826_;
goto v___jp_2815_;
}
v___jp_2815_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2817_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__36));
v___x_2818_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2813_, v___x_2814_);
v___x_2819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2817_);
lean_ctor_set(v___x_2819_, 1, v___x_2818_);
lean_inc(v___y_2816_);
v___x_2820_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___y_2816_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = 0;
v___x_2822_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set_uint8(v___x_2822_, sizeof(void*)*1, v___x_2821_);
v___x_2823_ = l_Repr_addAppParen(v___x_2822_, v_prec_2638_);
return v___x_2823_;
}
}
case 12:
{
lean_object* v_d_2827_; lean_object* v___x_2828_; lean_object* v___y_2830_; uint8_t v___x_2838_; 
v_d_2827_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_d_2827_);
lean_dec_ref_known(v_x_2637_, 3);
v___x_2828_ = lean_unsigned_to_nat(1024u);
v___x_2838_ = lean_nat_dec_le(v___x_2828_, v_prec_2638_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2830_ = v___x_2839_;
goto v___jp_2829_;
}
else
{
lean_object* v___x_2840_; 
v___x_2840_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2830_ = v___x_2840_;
goto v___jp_2829_;
}
v___jp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2831_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__41));
v___x_2832_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2827_, v___x_2828_);
v___x_2833_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
lean_inc(v___y_2830_);
v___x_2834_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___y_2830_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = 0;
v___x_2836_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set_uint8(v___x_2836_, sizeof(void*)*1, v___x_2835_);
v___x_2837_ = l_Repr_addAppParen(v___x_2836_, v_prec_2638_);
return v___x_2837_;
}
}
case 13:
{
lean_object* v_cost_2841_; lean_object* v_d_2842_; lean_object* v___x_2843_; lean_object* v___y_2845_; uint8_t v___x_2857_; 
v_cost_2841_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_cost_2841_);
v_d_2842_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_d_2842_);
lean_dec_ref_known(v_x_2637_, 3);
v___x_2843_ = lean_unsigned_to_nat(1024u);
v___x_2857_ = lean_nat_dec_le(v___x_2843_, v_prec_2638_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
v___x_2858_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2845_ = v___x_2858_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2859_; 
v___x_2859_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2845_ = v___x_2859_;
goto v___jp_2844_;
}
v___jp_2844_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2846_ = lean_box(1);
v___x_2847_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__44));
lean_inc_ref(v_inst_2636_);
v___x_2848_ = lean_apply_2(v_inst_2636_, v_cost_2841_, v___x_2843_);
v___x_2849_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___x_2846_);
v___x_2851_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_d_2842_, v___x_2843_);
v___x_2852_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2850_);
lean_ctor_set(v___x_2852_, 1, v___x_2851_);
lean_inc(v___y_2845_);
v___x_2853_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___y_2845_);
lean_ctor_set(v___x_2853_, 1, v___x_2852_);
v___x_2854_ = 0;
v___x_2855_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set_uint8(v___x_2855_, sizeof(void*)*1, v___x_2854_);
v___x_2856_ = l_Repr_addAppParen(v___x_2855_, v_prec_2638_);
return v___x_2856_;
}
}
case 14:
{
lean_object* v_a_2860_; lean_object* v_b_2861_; lean_object* v___x_2862_; lean_object* v___y_2864_; uint8_t v___x_2876_; 
v_a_2860_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_a_2860_);
v_b_2861_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_b_2861_);
lean_dec_ref_known(v_x_2637_, 3);
v___x_2862_ = lean_unsigned_to_nat(1024u);
v___x_2876_ = lean_nat_dec_le(v___x_2862_, v_prec_2638_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2864_ = v___x_2877_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2864_ = v___x_2878_;
goto v___jp_2863_;
}
v___jp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2865_ = lean_box(1);
v___x_2866_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__47));
lean_inc_ref(v_inst_2636_);
v___x_2867_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_a_2860_, v___x_2862_);
v___x_2868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2865_);
v___x_2870_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_b_2861_, v___x_2862_);
v___x_2871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
lean_inc(v___y_2864_);
v___x_2872_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___y_2864_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = 0;
v___x_2874_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set_uint8(v___x_2874_, sizeof(void*)*1, v___x_2873_);
v___x_2875_ = l_Repr_addAppParen(v___x_2874_, v_prec_2638_);
return v___x_2875_;
}
}
default: 
{
lean_object* v_a_2879_; lean_object* v_b_2880_; lean_object* v___x_2881_; lean_object* v___y_2883_; uint8_t v___x_2895_; 
v_a_2879_ = lean_ctor_get(v_x_2637_, 1);
lean_inc(v_a_2879_);
v_b_2880_ = lean_ctor_get(v_x_2637_, 2);
lean_inc(v_b_2880_);
lean_dec_ref_known(v_x_2637_, 3);
v___x_2881_ = lean_unsigned_to_nat(1024u);
v___x_2895_ = lean_nat_dec_le(v___x_2881_, v_prec_2638_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; 
v___x_2896_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2883_ = v___x_2896_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2883_ = v___x_2897_;
goto v___jp_2882_;
}
v___jp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2884_ = lean_box(1);
v___x_2885_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__50));
lean_inc_ref(v_inst_2636_);
v___x_2886_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_a_2879_, v___x_2881_);
v___x_2887_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___x_2888_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
lean_ctor_set(v___x_2888_, 1, v___x_2884_);
v___x_2889_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2636_, v_b_2880_, v___x_2881_);
v___x_2890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2888_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
lean_inc(v___y_2883_);
v___x_2891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___y_2883_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = 0;
v___x_2893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set_uint8(v___x_2893_, sizeof(void*)*1, v___x_2892_);
v___x_2894_ = l_Repr_addAppParen(v___x_2893_, v_prec_2638_);
return v___x_2894_;
}
}
}
v___jp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2641_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__1));
lean_inc(v___y_2640_);
v___x_2642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___y_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = 0;
v___x_2644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set_uint8(v___x_2644_, sizeof(void*)*1, v___x_2643_);
v___x_2645_ = l_Repr_addAppParen(v___x_2644_, v_prec_2638_);
return v___x_2645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___boxed(lean_object* v_inst_2898_, lean_object* v_x_2899_, lean_object* v_prec_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2898_, v_x_2899_, v_prec_2900_);
lean_dec(v_prec_2900_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr(lean_object* v_00_u03c4_2902_, lean_object* v_inst_2903_, lean_object* v_x_2904_, lean_object* v_prec_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2903_, v_x_2904_, v_prec_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___boxed(lean_object* v_00_u03c4_2907_, lean_object* v_inst_2908_, lean_object* v_x_2909_, lean_object* v_prec_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Fmt_instReprDoc_repr(v_00_u03c4_2907_, v_inst_2908_, v_x_2909_, v_prec_2910_);
lean_dec(v_prec_2910_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc___redArg(lean_object* v_inst_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2913_, 0, lean_box(0));
lean_closure_set(v___x_2913_, 1, v_inst_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc(lean_object* v_00_u03c4_2914_, lean_object* v_inst_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2916_, 0, lean_box(0));
lean_closure_set(v___x_2916_, 1, v_inst_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___redArg(lean_object* v_d_2917_, uint8_t v_fullness_2918_){
_start:
{
uint16_t v___x_2919_; uint16_t v___x_2920_; uint16_t v___x_2921_; uint16_t v___x_2922_; uint16_t v___x_2923_; uint16_t v___x_2924_; uint8_t v___x_2925_; 
v___x_2919_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2917_);
v___x_2920_ = lean_uint8_to_uint16(v_fullness_2918_);
v___x_2921_ = lean_uint16_shift_right(v___x_2919_, v___x_2920_);
v___x_2922_ = 1;
v___x_2923_ = lean_uint16_land(v___x_2921_, v___x_2922_);
v___x_2924_ = 0;
v___x_2925_ = lean_uint16_dec_eq(v___x_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
uint8_t v___x_2926_; 
v___x_2926_ = 1;
return v___x_2926_;
}
else
{
uint8_t v___x_2927_; 
v___x_2927_ = 0;
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___redArg___boxed(lean_object* v_d_2928_, lean_object* v_fullness_2929_){
_start:
{
uint8_t v_fullness_boxed_2930_; uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_fullness_boxed_2930_ = lean_unbox(v_fullness_2929_);
v_res_2931_ = l_Lean_Fmt_Doc_isFailure___redArg(v_d_2928_, v_fullness_boxed_2930_);
lean_dec(v_d_2928_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure(lean_object* v_00_u03c4_2933_, lean_object* v_d_2934_, uint8_t v_fullness_2935_){
_start:
{
uint8_t v___x_2936_; 
v___x_2936_ = l_Lean_Fmt_Doc_isFailure___redArg(v_d_2934_, v_fullness_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___boxed(lean_object* v_00_u03c4_2937_, lean_object* v_d_2938_, lean_object* v_fullness_2939_){
_start:
{
uint8_t v_fullness_boxed_2940_; uint8_t v_res_2941_; lean_object* v_r_2942_; 
v_fullness_boxed_2940_ = lean_unbox(v_fullness_2939_);
v_res_2941_ = l_Lean_Fmt_Doc_isFailure(v_00_u03c4_2937_, v_d_2938_, v_fullness_boxed_2940_);
lean_dec(v_d_2938_);
v_r_2942_ = lean_box(v_res_2941_);
return v_r_2942_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails___redArg(lean_object* v_d_2943_, uint8_t v_fullness_2944_){
_start:
{
uint16_t v___x_2945_; uint16_t v___x_2946_; uint16_t v___x_2947_; uint16_t v___x_2948_; uint16_t v___x_2949_; uint16_t v___x_2950_; uint8_t v___x_2951_; 
v___x_2945_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2943_);
v___x_2946_ = lean_uint8_to_uint16(v_fullness_2944_);
v___x_2947_ = lean_uint16_shift_right(v___x_2945_, v___x_2946_);
v___x_2948_ = 1;
v___x_2949_ = lean_uint16_land(v___x_2947_, v___x_2948_);
v___x_2950_ = 0;
v___x_2951_ = lean_uint16_dec_eq(v___x_2949_, v___x_2950_);
if (v___x_2951_ == 0)
{
uint8_t v___x_2952_; 
v___x_2952_ = 1;
return v___x_2952_;
}
else
{
uint8_t v___x_2953_; 
v___x_2953_ = 0;
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___redArg___boxed(lean_object* v_d_2954_, lean_object* v_fullness_2955_){
_start:
{
uint8_t v_fullness_boxed_2956_; uint8_t v_res_2957_; lean_object* v_r_2958_; 
v_fullness_boxed_2956_ = lean_unbox(v_fullness_2955_);
v_res_2957_ = l_Lean_Fmt_Doc_neverFails___redArg(v_d_2954_, v_fullness_boxed_2956_);
lean_dec(v_d_2954_);
v_r_2958_ = lean_box(v_res_2957_);
return v_r_2958_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_neverFails(lean_object* v_00_u03c4_2959_, lean_object* v_d_2960_, uint8_t v_fullness_2961_){
_start:
{
uint8_t v___x_2962_; 
v___x_2962_ = l_Lean_Fmt_Doc_neverFails___redArg(v_d_2960_, v_fullness_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_neverFails___boxed(lean_object* v_00_u03c4_2963_, lean_object* v_d_2964_, lean_object* v_fullness_2965_){
_start:
{
uint8_t v_fullness_boxed_2966_; uint8_t v_res_2967_; lean_object* v_r_2968_; 
v_fullness_boxed_2966_ = lean_unbox(v_fullness_2965_);
v_res_2967_ = l_Lean_Fmt_Doc_neverFails(v_00_u03c4_2963_, v_d_2964_, v_fullness_boxed_2966_);
lean_dec(v_d_2964_);
v_r_2968_ = lean_box(v_res_2967_);
return v_r_2968_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(lean_object* v_d_2969_, uint8_t v_fullness_2970_){
_start:
{
uint16_t v___x_2971_; uint16_t v___x_2972_; uint16_t v___x_2973_; uint16_t v___x_2974_; uint16_t v___x_2975_; uint16_t v___x_2976_; uint16_t v___x_2977_; uint16_t v___x_2978_; uint8_t v___x_2979_; 
v___x_2971_ = l_Lean_Fmt_Doc_failureSet___override___redArg(v_d_2969_);
v___x_2972_ = l_Lean_Fmt_Doc_neverFailsSet___override___redArg(v_d_2969_);
v___x_2973_ = lean_uint16_lor(v___x_2971_, v___x_2972_);
v___x_2974_ = lean_uint8_to_uint16(v_fullness_2970_);
v___x_2975_ = lean_uint16_shift_right(v___x_2973_, v___x_2974_);
v___x_2976_ = 1;
v___x_2977_ = lean_uint16_land(v___x_2975_, v___x_2976_);
v___x_2978_ = 0;
v___x_2979_ = lean_uint16_dec_eq(v___x_2977_, v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___redArg___boxed(lean_object* v_d_2980_, lean_object* v_fullness_2981_){
_start:
{
uint8_t v_fullness_boxed_2982_; uint8_t v_res_2983_; lean_object* v_r_2984_; 
v_fullness_boxed_2982_ = lean_unbox(v_fullness_2981_);
v_res_2983_ = l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(v_d_2980_, v_fullness_boxed_2982_);
lean_dec(v_d_2980_);
v_r_2984_ = lean_box(v_res_2983_);
return v_r_2984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_hasContextDependentFailure(lean_object* v_00_u03c4_2985_, lean_object* v_d_2986_, uint8_t v_fullness_2987_){
_start:
{
uint8_t v___x_2988_; 
v___x_2988_ = l_Lean_Fmt_Doc_hasContextDependentFailure___redArg(v_d_2986_, v_fullness_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hasContextDependentFailure___boxed(lean_object* v_00_u03c4_2989_, lean_object* v_d_2990_, lean_object* v_fullness_2991_){
_start:
{
uint8_t v_fullness_boxed_2992_; uint8_t v_res_2993_; lean_object* v_r_2994_; 
v_fullness_boxed_2992_ = lean_unbox(v_fullness_2991_);
v_res_2993_ = l_Lean_Fmt_Doc_hasContextDependentFailure(v_00_u03c4_2989_, v_d_2990_, v_fullness_boxed_2992_);
lean_dec(v_d_2990_);
v_r_2994_ = lean_box(v_res_2993_);
return v_r_2994_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object* v_d_2995_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2995_);
if (v___x_2996_ == 0)
{
uint8_t v___x_2997_; 
v___x_2997_ = 1;
return v___x_2997_;
}
else
{
uint8_t v___x_2998_; 
v___x_2998_ = 0;
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___redArg___boxed(lean_object* v_d_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_2999_);
lean_dec(v_d_2999_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty(lean_object* v_00_u03c4_3002_, lean_object* v_d_3003_){
_start:
{
uint8_t v___x_3004_; 
v___x_3004_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___boxed(lean_object* v_00_u03c4_3005_, lean_object* v_d_3006_){
_start:
{
uint8_t v_res_3007_; lean_object* v_r_3008_; 
v_res_3007_ = l_Lean_Fmt_Doc_isAlwaysEmpty(v_00_u03c4_3005_, v_d_3006_);
lean_dec(v_d_3006_);
v_r_3008_ = lean_box(v_res_3007_);
return v_r_3008_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object* v_d_3009_){
_start:
{
uint8_t v___x_3010_; 
v___x_3010_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_3009_);
if (v___x_3010_ == 0)
{
uint8_t v___x_3011_; 
v___x_3011_ = 1;
return v___x_3011_;
}
else
{
uint8_t v___x_3012_; 
v___x_3012_ = 0;
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg___boxed(lean_object* v_d_3013_){
_start:
{
uint8_t v_res_3014_; lean_object* v_r_3015_; 
v_res_3014_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_3013_);
lean_dec(v_d_3013_);
v_r_3015_ = lean_box(v_res_3014_);
return v_r_3015_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty(lean_object* v_00_u03c4_3016_, lean_object* v_d_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___boxed(lean_object* v_00_u03c4_3019_, lean_object* v_d_3020_){
_start:
{
uint8_t v_res_3021_; lean_object* v_r_3022_; 
v_res_3021_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty(v_00_u03c4_3019_, v_d_3020_);
lean_dec(v_d_3020_);
v_r_3022_ = lean_box(v_res_3021_);
return v_r_3022_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object* v_d_3023_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_3023_);
if (v___x_3024_ == 2)
{
uint8_t v___x_3025_; 
v___x_3025_ = 1;
return v___x_3025_;
}
else
{
if (v___x_3024_ == 0)
{
uint8_t v___x_3026_; 
v___x_3026_ = 1;
return v___x_3026_;
}
else
{
uint8_t v___x_3027_; 
v___x_3027_ = 0;
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___redArg___boxed(lean_object* v_d_3028_){
_start:
{
uint8_t v_res_3029_; lean_object* v_r_3030_; 
v_res_3029_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_3028_);
lean_dec(v_d_3028_);
v_r_3030_ = lean_box(v_res_3029_);
return v_r_3030_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic(lean_object* v_00_u03c4_3031_, lean_object* v_d_3032_){
_start:
{
uint8_t v___x_3033_; 
v___x_3033_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___boxed(lean_object* v_00_u03c4_3034_, lean_object* v_d_3035_){
_start:
{
uint8_t v_res_3036_; lean_object* v_r_3037_; 
v_res_3036_ = l_Lean_Fmt_Doc_isCompoundAtomic(v_00_u03c4_3034_, v_d_3035_);
lean_dec(v_d_3035_);
v_r_3037_ = lean_box(v_res_3036_);
return v_r_3037_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object* v_d_3038_){
_start:
{
uint8_t v___x_3039_; 
v___x_3039_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_3038_);
if (v___x_3039_ == 0)
{
uint8_t v___x_3040_; 
v___x_3040_ = 1;
return v___x_3040_;
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = 0;
return v___x_3041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___redArg___boxed(lean_object* v_d_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_3042_);
lean_dec(v_d_3042_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic(lean_object* v_00_u03c4_3045_, lean_object* v_d_3046_){
_start:
{
uint8_t v___x_3047_; 
v___x_3047_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___boxed(lean_object* v_00_u03c4_3048_, lean_object* v_d_3049_){
_start:
{
uint8_t v_res_3050_; lean_object* v_r_3051_; 
v_res_3050_ = l_Lean_Fmt_Doc_isAtomic(v_00_u03c4_3048_, v_d_3049_);
lean_dec(v_d_3049_);
v_r_3051_ = lean_box(v_res_3050_);
return v_r_3051_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___redArg___closed__0));
v___x_3054_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg(){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty___redArg___boxed(lean_object* v___dummy_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_Fmt_Doc_empty___redArg();
return v_res_3058_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___closed__0(void){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_Fmt_Doc_empty___redArg();
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object* v_00_u03c4_3060_){
_start:
{
lean_object* v___x_3061_; 
v___x_3061_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object* v_d_3062_){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_inc(v_d_3062_);
v___x_3063_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_3062_);
v___x_3064_ = l_Lean_Fmt_Doc_either___override___redArg(v_d_3062_, v___x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object* v_00_u03c4_3065_, lean_object* v_d_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Lean_Fmt_Doc_maybeFlattened___redArg(v_d_3066_);
return v___x_3067_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___redArg___closed__1(void){
_start:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___redArg___closed__0));
v___x_3070_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_3069_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg(){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___redArg___closed__1, &l_Lean_Fmt_Doc_nl___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_nl___redArg___closed__1);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl___redArg___boxed(lean_object* v___dummy_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Fmt_Doc_nl___redArg();
return v_res_3074_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___closed__0(void){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_Fmt_Doc_nl___redArg();
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object* v_00_u03c4_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___redArg___closed__0(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___redArg___closed__0));
v___x_3079_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_3078_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg(){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_obj_once(&l_Lean_Fmt_Doc_break___redArg___closed__0, &l_Lean_Fmt_Doc_break___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_break___redArg___closed__0);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break___redArg___boxed(lean_object* v___dummy_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_Fmt_Doc_break___redArg();
return v_res_3083_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___closed__0(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Fmt_Doc_break___redArg();
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object* v_00_u03c4_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_obj_once(&l_Lean_Fmt_Doc_break___closed__0, &l_Lean_Fmt_Doc_break___closed__0_once, _init_l_Lean_Fmt_Doc_break___closed__0);
return v___x_3086_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___redArg___closed__0(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v___x_3088_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg(){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___redArg___closed__0, &l_Lean_Fmt_Doc_hardNl___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___redArg___closed__0);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl___redArg___boxed(lean_object* v___dummy_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v_res_3092_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_Lean_Fmt_Doc_hardNl___redArg();
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object* v_00_u03c4_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object* v_d_3096_){
_start:
{
lean_object* v___x_3097_; uint8_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = lean_unsigned_to_nat(2u);
v___x_3098_ = 0;
v___x_3099_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_3097_, v___x_3098_, v_d_3096_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object* v_00_u03c4_3100_, lean_object* v_d_3101_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_Fmt_Doc_nested___redArg(v_d_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object* v_d_3103_){
_start:
{
lean_object* v___x_3104_; uint8_t v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = lean_unsigned_to_nat(2u);
v___x_3105_ = 1;
v___x_3106_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_3104_, v___x_3105_, v_d_3103_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object* v_00_u03c4_3107_, lean_object* v_d_3108_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_Fmt_Doc_hardNested___redArg(v_d_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object* v_a_3110_, lean_object* v_b_3111_){
_start:
{
lean_object* v_array_3112_; lean_object* v_start_3113_; lean_object* v_stop_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3127_; 
v_array_3112_ = lean_ctor_get(v_a_3110_, 0);
v_start_3113_ = lean_ctor_get(v_a_3110_, 1);
v_stop_3114_ = lean_ctor_get(v_a_3110_, 2);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_a_3110_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3116_ = v_a_3110_;
v_isShared_3117_ = v_isSharedCheck_3127_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_stop_3114_);
lean_inc(v_start_3113_);
lean_inc(v_array_3112_);
lean_dec(v_a_3110_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3127_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
uint8_t v___x_3118_; 
v___x_3118_ = lean_nat_dec_lt(v_start_3113_, v_stop_3114_);
if (v___x_3118_ == 0)
{
lean_del_object(v___x_3116_);
lean_dec(v_stop_3114_);
lean_dec(v_start_3113_);
lean_dec_ref(v_array_3112_);
return v_b_3111_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3119_ = lean_unsigned_to_nat(1u);
v___x_3120_ = lean_nat_add(v_start_3113_, v___x_3119_);
lean_inc_ref(v_array_3112_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 1, v___x_3120_);
v___x_3122_ = v___x_3116_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_array_3112_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_stop_3114_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
v___x_3123_ = lean_array_fget(v_array_3112_, v_start_3113_);
lean_dec(v_start_3113_);
lean_dec_ref(v_array_3112_);
v___x_3124_ = l_Lean_Fmt_Doc_either___override___redArg(v_b_3111_, v___x_3123_);
v_a_3110_ = v___x_3122_;
v_b_3111_ = v___x_3124_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object* v_ds_3128_){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_array_get_size(v_ds_3128_);
v___x_3131_ = lean_nat_dec_lt(v___x_3129_, v___x_3130_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
lean_dec_ref(v_ds_3128_);
v___x_3132_ = lean_box(0);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3133_ = lean_array_fget(v_ds_3128_, v___x_3129_);
v___x_3134_ = lean_unsigned_to_nat(1u);
v___x_3135_ = l_Array_toSubarray___redArg(v_ds_3128_, v___x_3134_, v___x_3130_);
v___x_3136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v___x_3135_, v___x_3133_);
return v___x_3136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object* v_00_u03c4_3137_, lean_object* v_ds_3138_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Lean_Fmt_Doc_oneOf___redArg(v_ds_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object* v_00_u03c4_3140_, lean_object* v_inst_3141_, lean_object* v_R_3142_, lean_object* v_a_3143_, lean_object* v_b_3144_, lean_object* v_c_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v_a_3143_, v_b_3144_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___lam__0(lean_object* v_d1_3147_, lean_object* v_d2_3148_){
_start:
{
uint8_t v___x_3149_; 
v___x_3149_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d1_3147_);
if (v___x_3149_ == 0)
{
uint8_t v___x_3150_; 
v___x_3150_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d2_3148_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_Fmt_Doc_append___override___redArg(v_d1_3147_, v_d2_3148_);
return v___x_3151_;
}
else
{
lean_dec(v_d2_3148_);
return v_d1_3147_;
}
}
else
{
lean_dec(v_d1_3147_);
return v_d2_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg(){
_start:
{
lean_object* v___f_3154_; 
v___f_3154_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___redArg___closed__0));
return v___f_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___redArg___boxed(lean_object* v___dummy_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Fmt_instAppendDoc___redArg();
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object* v_00_u03c4_3157_){
_start:
{
lean_object* v___f_3158_; 
v___f_3158_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___redArg___closed__0));
return v___f_3158_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object* v_a_3159_, lean_object* v_b_3160_){
_start:
{
lean_object* v_array_3161_; lean_object* v_start_3162_; lean_object* v_stop_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3180_; 
v_array_3161_ = lean_ctor_get(v_a_3159_, 0);
v_start_3162_ = lean_ctor_get(v_a_3159_, 1);
v_stop_3163_ = lean_ctor_get(v_a_3159_, 2);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_a_3159_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3165_ = v_a_3159_;
v_isShared_3166_ = v_isSharedCheck_3180_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_stop_3163_);
lean_inc(v_start_3162_);
lean_inc(v_array_3161_);
lean_dec(v_a_3159_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3180_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
uint8_t v___x_3167_; 
v___x_3167_ = lean_nat_dec_lt(v_start_3162_, v_stop_3163_);
if (v___x_3167_ == 0)
{
lean_del_object(v___x_3165_);
lean_dec(v_stop_3163_);
lean_dec(v_start_3162_);
lean_dec_ref(v_array_3161_);
return v_b_3160_;
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3168_ = lean_unsigned_to_nat(1u);
v___x_3169_ = lean_nat_add(v_start_3162_, v___x_3168_);
lean_inc_ref(v_array_3161_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 1, v___x_3169_);
v___x_3171_ = v___x_3165_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_array_3161_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_stop_3163_);
v___x_3171_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; uint8_t v___x_3173_; 
v___x_3172_ = lean_array_fget(v_array_3161_, v_start_3162_);
lean_dec(v_start_3162_);
lean_dec_ref(v_array_3161_);
v___x_3173_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_3160_);
if (v___x_3173_ == 0)
{
uint8_t v___x_3174_; 
v___x_3174_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_3172_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_3160_, v___x_3172_);
v_a_3159_ = v___x_3171_;
v_b_3160_ = v___x_3175_;
goto _start;
}
else
{
lean_dec(v___x_3172_);
v_a_3159_ = v___x_3171_;
goto _start;
}
}
else
{
lean_dec(v_b_3160_);
v_a_3159_ = v___x_3171_;
v_b_3160_ = v___x_3172_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object* v_ds_3181_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_array_get_size(v_ds_3181_);
v___x_3184_ = lean_nat_dec_lt(v___x_3182_, v___x_3183_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
lean_dec_ref(v_ds_3181_);
v___x_3185_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3185_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3186_ = lean_array_fget(v_ds_3181_, v___x_3182_);
v___x_3187_ = lean_unsigned_to_nat(1u);
v___x_3188_ = l_Array_toSubarray___redArg(v_ds_3181_, v___x_3187_, v___x_3183_);
v___x_3189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v___x_3188_, v___x_3186_);
return v___x_3189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object* v_00_u03c4_3190_, lean_object* v_ds_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_Fmt_Doc_join___redArg(v_ds_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object* v_00_u03c4_3193_, lean_object* v_inst_3194_, lean_object* v_R_3195_, lean_object* v_a_3196_, lean_object* v_b_3197_, lean_object* v_c_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v_a_3196_, v_b_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object* v_sep_3200_, lean_object* v_a_3201_, lean_object* v_b_3202_){
_start:
{
lean_object* v_array_3203_; lean_object* v_start_3204_; lean_object* v_stop_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3227_; 
v_array_3203_ = lean_ctor_get(v_a_3201_, 0);
v_start_3204_ = lean_ctor_get(v_a_3201_, 1);
v_stop_3205_ = lean_ctor_get(v_a_3201_, 2);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3207_ = v_a_3201_;
v_isShared_3208_ = v_isSharedCheck_3227_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_stop_3205_);
lean_inc(v_start_3204_);
lean_inc(v_array_3203_);
lean_dec(v_a_3201_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3227_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
uint8_t v___x_3209_; 
v___x_3209_ = lean_nat_dec_lt(v_start_3204_, v_stop_3205_);
if (v___x_3209_ == 0)
{
lean_del_object(v___x_3207_);
lean_dec(v_stop_3205_);
lean_dec(v_start_3204_);
lean_dec_ref(v_array_3203_);
lean_dec(v_sep_3200_);
return v_b_3202_;
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v___x_3210_ = lean_unsigned_to_nat(1u);
v___x_3211_ = lean_nat_add(v_start_3204_, v___x_3210_);
lean_inc_ref(v_array_3203_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3211_);
v___x_3213_ = v___x_3207_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_array_3203_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_stop_3205_);
v___x_3213_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; lean_object* v___y_3216_; uint8_t v___x_3223_; 
v___x_3214_ = lean_array_fget(v_array_3203_, v_start_3204_);
lean_dec(v_start_3204_);
lean_dec_ref(v_array_3203_);
v___x_3223_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_3202_);
if (v___x_3223_ == 0)
{
uint8_t v___x_3224_; 
v___x_3224_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_sep_3200_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; 
lean_inc(v_sep_3200_);
v___x_3225_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_3202_, v_sep_3200_);
v___y_3216_ = v___x_3225_;
goto v___jp_3215_;
}
else
{
v___y_3216_ = v_b_3202_;
goto v___jp_3215_;
}
}
else
{
lean_dec(v_b_3202_);
lean_inc(v_sep_3200_);
v___y_3216_ = v_sep_3200_;
goto v___jp_3215_;
}
v___jp_3215_:
{
uint8_t v___x_3217_; 
v___x_3217_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___y_3216_);
if (v___x_3217_ == 0)
{
uint8_t v___x_3218_; 
v___x_3218_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_3214_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Fmt_Doc_append___override___redArg(v___y_3216_, v___x_3214_);
v_a_3201_ = v___x_3213_;
v_b_3202_ = v___x_3219_;
goto _start;
}
else
{
lean_dec(v___x_3214_);
v_a_3201_ = v___x_3213_;
v_b_3202_ = v___y_3216_;
goto _start;
}
}
else
{
lean_dec(v___y_3216_);
v_a_3201_ = v___x_3213_;
v_b_3202_ = v___x_3214_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object* v_sep_3228_, lean_object* v_ds_3229_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3230_ = lean_unsigned_to_nat(0u);
v___x_3231_ = lean_array_get_size(v_ds_3229_);
v___x_3232_ = lean_nat_dec_lt(v___x_3230_, v___x_3231_);
if (v___x_3232_ == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref(v_ds_3229_);
lean_dec(v_sep_3228_);
v___x_3233_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___redArg___closed__1, &l_Lean_Fmt_Doc_empty___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_empty___redArg___closed__1);
return v___x_3233_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3234_ = lean_array_fget(v_ds_3229_, v___x_3230_);
v___x_3235_ = lean_unsigned_to_nat(1u);
v___x_3236_ = l_Array_toSubarray___redArg(v_ds_3229_, v___x_3235_, v___x_3231_);
v___x_3237_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_3228_, v___x_3236_, v___x_3234_);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object* v_00_u03c4_3238_, lean_object* v_sep_3239_, lean_object* v_ds_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_sep_3239_, v_ds_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object* v_00_u03c4_3242_, lean_object* v_sep_3243_, lean_object* v_inst_3244_, lean_object* v_R_3245_, lean_object* v_a_3246_, lean_object* v_b_3247_, lean_object* v_c_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_3243_, v_a_3246_, v_b_3247_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(lean_object* v_a_3250_, lean_object* v_b_3251_){
_start:
{
lean_object* v_array_3252_; lean_object* v_start_3253_; lean_object* v_stop_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3295_; 
v_array_3252_ = lean_ctor_get(v_a_3250_, 0);
v_start_3253_ = lean_ctor_get(v_a_3250_, 1);
v_stop_3254_ = lean_ctor_get(v_a_3250_, 2);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_a_3250_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3256_ = v_a_3250_;
v_isShared_3257_ = v_isSharedCheck_3295_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_stop_3254_);
lean_inc(v_start_3253_);
lean_inc(v_array_3252_);
lean_dec(v_a_3250_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3295_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
uint8_t v___x_3258_; 
v___x_3258_ = lean_nat_dec_lt(v_start_3253_, v_stop_3254_);
if (v___x_3258_ == 0)
{
lean_del_object(v___x_3256_);
lean_dec(v_stop_3254_);
lean_dec(v_start_3253_);
lean_dec_ref(v_array_3252_);
return v_b_3251_;
}
else
{
lean_object* v_fst_3259_; lean_object* v_snd_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3294_; 
v_fst_3259_ = lean_ctor_get(v_b_3251_, 0);
v_snd_3260_ = lean_ctor_get(v_b_3251_, 1);
v_isSharedCheck_3294_ = !lean_is_exclusive(v_b_3251_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3262_ = v_b_3251_;
v_isShared_3263_ = v_isSharedCheck_3294_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_snd_3260_);
lean_inc(v_fst_3259_);
lean_dec(v_b_3251_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3294_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3264_ = lean_unsigned_to_nat(1u);
v___x_3265_ = lean_nat_add(v_start_3253_, v___x_3264_);
lean_inc_ref(v_array_3252_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 1, v___x_3265_);
v___x_3267_ = v___x_3256_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_array_3252_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_stop_3254_);
v___x_3267_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3268_ = lean_array_fget(v_array_3252_, v_start_3253_);
lean_dec(v_start_3253_);
lean_dec_ref(v_array_3252_);
v___x_3269_ = lean_unsigned_to_nat(2u);
v___x_3270_ = lean_mk_empty_array_with_capacity(v___x_3269_);
lean_inc_ref(v___x_3270_);
v___x_3271_ = lean_array_push(v___x_3270_, v_fst_3259_);
lean_inc_ref(v___x_3271_);
v___x_3272_ = lean_array_push(v___x_3271_, v_snd_3260_);
v___x_3273_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3272_);
lean_inc(v___x_3268_);
v___x_3274_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_3268_);
lean_inc(v___x_3274_);
v___x_3275_ = lean_array_push(v___x_3271_, v___x_3274_);
v___x_3276_ = l_Lean_Fmt_Doc_join___redArg(v___x_3275_);
v___x_3277_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3278_ = lean_unsigned_to_nat(3u);
v___x_3279_ = lean_mk_empty_array_with_capacity(v___x_3278_);
v___x_3280_ = lean_array_push(v___x_3279_, v___x_3273_);
v___x_3281_ = lean_array_push(v___x_3280_, v___x_3277_);
lean_inc_ref(v___x_3281_);
v___x_3282_ = lean_array_push(v___x_3281_, v___x_3274_);
v___x_3283_ = l_Lean_Fmt_Doc_join___redArg(v___x_3282_);
v___x_3284_ = lean_array_push(v___x_3270_, v___x_3276_);
v___x_3285_ = lean_array_push(v___x_3284_, v___x_3283_);
v___x_3286_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3285_);
v___x_3287_ = lean_array_push(v___x_3281_, v___x_3268_);
v___x_3288_ = l_Lean_Fmt_Doc_join___redArg(v___x_3287_);
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 1, v___x_3288_);
lean_ctor_set(v___x_3262_, 0, v___x_3286_);
v___x_3290_ = v___x_3262_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3292_, 1, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
v_a_3250_ = v___x_3267_;
v_b_3251_ = v___x_3290_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object* v_ds_3296_){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3297_ = lean_array_get_size(v_ds_3296_);
v___x_3298_ = lean_unsigned_to_nat(0u);
v___x_3299_ = lean_nat_dec_eq(v___x_3297_, v___x_3298_);
if (v___x_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v_lastNotFlattened_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3300_ = lean_box(0);
v_lastNotFlattened_3301_ = lean_array_get(v___x_3300_, v_ds_3296_, v___x_3298_);
v___x_3302_ = lean_unsigned_to_nat(1u);
v___x_3303_ = lean_nat_dec_eq(v___x_3297_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_object* v_lastFlattened_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
lean_inc(v_lastNotFlattened_3301_);
v_lastFlattened_3304_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_3301_);
v___x_3305_ = l_Array_toSubarray___redArg(v_ds_3296_, v___x_3302_, v___x_3297_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_lastFlattened_3304_);
lean_ctor_set(v___x_3306_, 1, v_lastNotFlattened_3301_);
v___x_3307_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(v___x_3305_, v___x_3306_);
v_fst_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_fst_3308_);
v_snd_3309_ = lean_ctor_get(v___x_3307_, 1);
lean_inc(v_snd_3309_);
lean_dec_ref(v___x_3307_);
v___x_3310_ = lean_unsigned_to_nat(2u);
v___x_3311_ = lean_mk_empty_array_with_capacity(v___x_3310_);
v___x_3312_ = lean_array_push(v___x_3311_, v_fst_3308_);
v___x_3313_ = lean_array_push(v___x_3312_, v_snd_3309_);
v___x_3314_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3313_);
return v___x_3314_;
}
else
{
lean_dec_ref(v_ds_3296_);
return v_lastNotFlattened_3301_;
}
}
else
{
lean_object* v___x_3315_; 
lean_dec_ref(v_ds_3296_);
v___x_3315_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill(lean_object* v_00_u03c4_3316_, lean_object* v_ds_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Fmt_Doc_fill___redArg(v_ds_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0(lean_object* v_00_u03c4_3319_, lean_object* v_inst_3320_, lean_object* v_R_3321_, lean_object* v_a_3322_, lean_object* v_b_3323_, lean_object* v_c_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(v_a_3322_, v_b_3323_);
return v___x_3325_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3326_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3327_ = lean_unsigned_to_nat(2u);
v___x_3328_ = lean_mk_empty_array_with_capacity(v___x_3327_);
v___x_3329_ = lean_array_push(v___x_3328_, v___x_3326_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(lean_object* v_wrap_3330_, lean_object* v_as_3331_, size_t v_sz_3332_, size_t v_i_3333_, lean_object* v_b_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_lt(v_i_3333_, v_sz_3332_);
if (v___x_3335_ == 0)
{
lean_dec_ref(v_wrap_3330_);
return v_b_3334_;
}
else
{
lean_object* v_fst_3336_; lean_object* v_snd_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3370_; 
v_fst_3336_ = lean_ctor_get(v_b_3334_, 0);
v_snd_3337_ = lean_ctor_get(v_b_3334_, 1);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_b_3334_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3339_ = v_b_3334_;
v_isShared_3340_ = v_isSharedCheck_3370_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snd_3337_);
lean_inc(v_fst_3336_);
lean_dec(v_b_3334_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3370_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v_a_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v_a_3341_ = lean_array_uget_borrowed(v_as_3331_, v_i_3333_);
v___x_3342_ = lean_unsigned_to_nat(2u);
v___x_3343_ = lean_mk_empty_array_with_capacity(v___x_3342_);
lean_inc(v_fst_3336_);
lean_inc_ref_n(v___x_3343_, 3);
v___x_3344_ = lean_array_push(v___x_3343_, v_fst_3336_);
v___x_3345_ = lean_array_push(v___x_3344_, v_snd_3337_);
v___x_3346_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3345_);
v___x_3347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_3348_ = lean_array_push(v___x_3347_, v___x_3346_);
v___x_3349_ = l_Lean_Fmt_Doc_join___redArg(v___x_3348_);
lean_inc_ref_n(v_wrap_3330_, 2);
v___x_3350_ = lean_apply_1(v_wrap_3330_, v___x_3349_);
lean_inc_n(v_a_3341_, 2);
v___x_3351_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_a_3341_);
v___x_3352_ = lean_apply_1(v_wrap_3330_, v_fst_3336_);
v___x_3353_ = lean_array_push(v___x_3343_, v___x_3351_);
lean_inc_ref(v___x_3353_);
v___x_3354_ = lean_array_push(v___x_3353_, v___x_3352_);
v___x_3355_ = l_Lean_Fmt_Doc_join___redArg(v___x_3354_);
lean_inc(v___x_3350_);
v___x_3356_ = lean_array_push(v___x_3353_, v___x_3350_);
v___x_3357_ = l_Lean_Fmt_Doc_join___redArg(v___x_3356_);
v___x_3358_ = lean_array_push(v___x_3343_, v___x_3355_);
v___x_3359_ = lean_array_push(v___x_3358_, v___x_3357_);
v___x_3360_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3359_);
v___x_3361_ = lean_array_push(v___x_3343_, v_a_3341_);
v___x_3362_ = lean_array_push(v___x_3361_, v___x_3350_);
v___x_3363_ = l_Lean_Fmt_Doc_join___redArg(v___x_3362_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v___x_3363_);
lean_ctor_set(v___x_3339_, 0, v___x_3360_);
v___x_3365_ = v___x_3339_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
size_t v___x_3366_; size_t v___x_3367_; 
v___x_3366_ = ((size_t)1ULL);
v___x_3367_ = lean_usize_add(v_i_3333_, v___x_3366_);
v_i_3333_ = v___x_3367_;
v_b_3334_ = v___x_3365_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___boxed(lean_object* v_wrap_3371_, lean_object* v_as_3372_, lean_object* v_sz_3373_, lean_object* v_i_3374_, lean_object* v_b_3375_){
_start:
{
size_t v_sz_boxed_3376_; size_t v_i_boxed_3377_; lean_object* v_res_3378_; 
v_sz_boxed_3376_ = lean_unbox_usize(v_sz_3373_);
lean_dec(v_sz_3373_);
v_i_boxed_3377_ = lean_unbox_usize(v_i_3374_);
lean_dec(v_i_3374_);
v_res_3378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_3371_, v_as_3372_, v_sz_boxed_3376_, v_i_boxed_3377_, v_b_3375_);
lean_dec_ref(v_as_3372_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object* v_ds_3379_, lean_object* v_wrap_3380_){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3381_ = lean_array_get_size(v_ds_3379_);
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_nat_dec_eq(v___x_3381_, v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v_restNotFlattened_3387_; uint8_t v___x_3388_; 
v___x_3384_ = lean_box(0);
v___x_3385_ = lean_unsigned_to_nat(1u);
v___x_3386_ = lean_nat_sub(v___x_3381_, v___x_3385_);
v_restNotFlattened_3387_ = lean_array_get(v___x_3384_, v_ds_3379_, v___x_3386_);
lean_dec(v___x_3386_);
v___x_3388_ = lean_nat_dec_eq(v___x_3381_, v___x_3385_);
if (v___x_3388_ == 0)
{
lean_object* v_restFlattened_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; size_t v_sz_3393_; size_t v___x_3394_; lean_object* v___x_3395_; lean_object* v_fst_3396_; lean_object* v_snd_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
lean_inc(v_restNotFlattened_3387_);
v_restFlattened_3389_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_3387_);
v___x_3390_ = lean_array_pop(v_ds_3379_);
v___x_3391_ = l_Array_reverse___redArg(v___x_3390_);
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v_restFlattened_3389_);
lean_ctor_set(v___x_3392_, 1, v_restNotFlattened_3387_);
v_sz_3393_ = lean_array_size(v___x_3391_);
v___x_3394_ = ((size_t)0ULL);
v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_3380_, v___x_3391_, v_sz_3393_, v___x_3394_, v___x_3392_);
lean_dec_ref(v___x_3391_);
v_fst_3396_ = lean_ctor_get(v___x_3395_, 0);
lean_inc(v_fst_3396_);
v_snd_3397_ = lean_ctor_get(v___x_3395_, 1);
lean_inc(v_snd_3397_);
lean_dec_ref(v___x_3395_);
v___x_3398_ = lean_unsigned_to_nat(2u);
v___x_3399_ = lean_mk_empty_array_with_capacity(v___x_3398_);
v___x_3400_ = lean_array_push(v___x_3399_, v_fst_3396_);
v___x_3401_ = lean_array_push(v___x_3400_, v_snd_3397_);
v___x_3402_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3401_);
return v___x_3402_;
}
else
{
lean_dec_ref(v_wrap_3380_);
lean_dec_ref(v_ds_3379_);
return v_restNotFlattened_3387_;
}
}
else
{
lean_object* v___x_3403_; 
lean_dec_ref(v_wrap_3380_);
lean_dec_ref(v_ds_3379_);
v___x_3403_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping(lean_object* v_00_u03c4_3404_, lean_object* v_ds_3405_, lean_object* v_wrap_3406_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_ds_3405_, v_wrap_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0(lean_object* v_00_u03c4_3408_, lean_object* v_wrap_3409_, lean_object* v_as_3410_, size_t v_sz_3411_, size_t v_i_3412_, lean_object* v_b_3413_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_3409_, v_as_3410_, v_sz_3411_, v_i_3412_, v_b_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___boxed(lean_object* v_00_u03c4_3415_, lean_object* v_wrap_3416_, lean_object* v_as_3417_, lean_object* v_sz_3418_, lean_object* v_i_3419_, lean_object* v_b_3420_){
_start:
{
size_t v_sz_boxed_3421_; size_t v_i_boxed_3422_; lean_object* v_res_3423_; 
v_sz_boxed_3421_ = lean_unbox_usize(v_sz_3418_);
lean_dec(v_sz_3418_);
v_i_boxed_3422_ = lean_unbox_usize(v_i_3419_);
lean_dec(v_i_3419_);
v_res_3423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0(v_00_u03c4_3415_, v_wrap_3416_, v_as_3417_, v_sz_boxed_3421_, v_i_boxed_3422_, v_b_3420_);
lean_dec_ref(v_as_3417_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(lean_object* v_sep_3424_, lean_object* v_a_3425_, lean_object* v_b_3426_){
_start:
{
lean_object* v_array_3427_; lean_object* v_start_3428_; lean_object* v_stop_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3475_; 
v_array_3427_ = lean_ctor_get(v_a_3425_, 0);
v_start_3428_ = lean_ctor_get(v_a_3425_, 1);
v_stop_3429_ = lean_ctor_get(v_a_3425_, 2);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_a_3425_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3431_ = v_a_3425_;
v_isShared_3432_ = v_isSharedCheck_3475_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_stop_3429_);
lean_inc(v_start_3428_);
lean_inc(v_array_3427_);
lean_dec(v_a_3425_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3475_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
uint8_t v___x_3433_; 
v___x_3433_ = lean_nat_dec_lt(v_start_3428_, v_stop_3429_);
if (v___x_3433_ == 0)
{
lean_del_object(v___x_3431_);
lean_dec(v_stop_3429_);
lean_dec(v_start_3428_);
lean_dec_ref(v_array_3427_);
lean_dec(v_sep_3424_);
return v_b_3426_;
}
else
{
lean_object* v_fst_3434_; lean_object* v_snd_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3474_; 
v_fst_3434_ = lean_ctor_get(v_b_3426_, 0);
v_snd_3435_ = lean_ctor_get(v_b_3426_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_b_3426_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3437_ = v_b_3426_;
v_isShared_3438_ = v_isSharedCheck_3474_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_snd_3435_);
lean_inc(v_fst_3434_);
lean_dec(v_b_3426_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3474_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3439_ = lean_unsigned_to_nat(1u);
v___x_3440_ = lean_nat_add(v_start_3428_, v___x_3439_);
lean_inc_ref(v_array_3427_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3440_);
v___x_3442_ = v___x_3431_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_array_3427_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_stop_3429_);
v___x_3442_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3443_ = lean_array_fget(v_array_3427_, v_start_3428_);
lean_dec(v_start_3428_);
lean_dec_ref(v_array_3427_);
v___x_3444_ = lean_unsigned_to_nat(2u);
v___x_3445_ = lean_mk_empty_array_with_capacity(v___x_3444_);
lean_inc(v_fst_3434_);
lean_inc_ref(v___x_3445_);
v___x_3446_ = lean_array_push(v___x_3445_, v_fst_3434_);
v___x_3447_ = lean_array_push(v___x_3446_, v_snd_3435_);
v___x_3448_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3447_);
lean_inc(v___x_3443_);
v___x_3449_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_3443_);
v___x_3450_ = lean_unsigned_to_nat(3u);
v___x_3451_ = lean_mk_empty_array_with_capacity(v___x_3450_);
v___x_3452_ = lean_array_push(v___x_3451_, v_fst_3434_);
lean_inc_n(v_sep_3424_, 2);
v___x_3453_ = lean_array_push(v___x_3452_, v_sep_3424_);
lean_inc(v___x_3449_);
v___x_3454_ = lean_array_push(v___x_3453_, v___x_3449_);
v___x_3455_ = l_Lean_Fmt_Doc_join___redArg(v___x_3454_);
v___x_3456_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3457_ = lean_unsigned_to_nat(4u);
v___x_3458_ = lean_mk_empty_array_with_capacity(v___x_3457_);
v___x_3459_ = lean_array_push(v___x_3458_, v___x_3448_);
v___x_3460_ = lean_array_push(v___x_3459_, v_sep_3424_);
v___x_3461_ = lean_array_push(v___x_3460_, v___x_3456_);
lean_inc_ref(v___x_3461_);
v___x_3462_ = lean_array_push(v___x_3461_, v___x_3449_);
v___x_3463_ = l_Lean_Fmt_Doc_join___redArg(v___x_3462_);
v___x_3464_ = lean_array_push(v___x_3445_, v___x_3455_);
v___x_3465_ = lean_array_push(v___x_3464_, v___x_3463_);
v___x_3466_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3465_);
v___x_3467_ = lean_array_push(v___x_3461_, v___x_3443_);
v___x_3468_ = l_Lean_Fmt_Doc_join___redArg(v___x_3467_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 1, v___x_3468_);
lean_ctor_set(v___x_3437_, 0, v___x_3466_);
v___x_3470_ = v___x_3437_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
v_a_3425_ = v___x_3442_;
v_b_3426_ = v___x_3470_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object* v_sep_3476_, lean_object* v_ds_3477_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3478_ = lean_array_get_size(v_ds_3477_);
v___x_3479_ = lean_unsigned_to_nat(0u);
v___x_3480_ = lean_nat_dec_eq(v___x_3478_, v___x_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; lean_object* v_lastNotFlattened_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3481_ = lean_box(0);
v_lastNotFlattened_3482_ = lean_array_get(v___x_3481_, v_ds_3477_, v___x_3479_);
v___x_3483_ = lean_unsigned_to_nat(1u);
v___x_3484_ = lean_nat_dec_eq(v___x_3478_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v_lastFlattened_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v_fst_3489_; lean_object* v_snd_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
lean_inc(v_lastNotFlattened_3482_);
v_lastFlattened_3485_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_3482_);
v___x_3486_ = l_Array_toSubarray___redArg(v_ds_3477_, v___x_3483_, v___x_3478_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_lastFlattened_3485_);
lean_ctor_set(v___x_3487_, 1, v_lastNotFlattened_3482_);
v___x_3488_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(v_sep_3476_, v___x_3486_, v___x_3487_);
v_fst_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_fst_3489_);
v_snd_3490_ = lean_ctor_get(v___x_3488_, 1);
lean_inc(v_snd_3490_);
lean_dec_ref(v___x_3488_);
v___x_3491_ = lean_unsigned_to_nat(2u);
v___x_3492_ = lean_mk_empty_array_with_capacity(v___x_3491_);
v___x_3493_ = lean_array_push(v___x_3492_, v_fst_3489_);
v___x_3494_ = lean_array_push(v___x_3493_, v_snd_3490_);
v___x_3495_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3494_);
return v___x_3495_;
}
else
{
lean_dec_ref(v_ds_3477_);
lean_dec(v_sep_3476_);
return v_lastNotFlattened_3482_;
}
}
else
{
lean_object* v___x_3496_; 
lean_dec_ref(v_ds_3477_);
lean_dec(v_sep_3476_);
v___x_3496_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing(lean_object* v_00_u03c4_3497_, lean_object* v_sep_3498_, lean_object* v_ds_3499_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_3498_, v_ds_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0(lean_object* v_00_u03c4_3501_, lean_object* v_sep_3502_, lean_object* v_inst_3503_, lean_object* v_R_3504_, lean_object* v_a_3505_, lean_object* v_b_3506_, lean_object* v_c_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(v_sep_3502_, v_a_3505_, v_b_3506_);
return v___x_3508_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___redArg___closed__0));
v___x_3510_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_3509_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(lean_object* v_a_3511_, lean_object* v_b_3512_){
_start:
{
lean_object* v_array_3513_; lean_object* v_start_3514_; lean_object* v_stop_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3559_; 
v_array_3513_ = lean_ctor_get(v_a_3511_, 0);
v_start_3514_ = lean_ctor_get(v_a_3511_, 1);
v_stop_3515_ = lean_ctor_get(v_a_3511_, 2);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_a_3511_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3517_ = v_a_3511_;
v_isShared_3518_ = v_isSharedCheck_3559_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_stop_3515_);
lean_inc(v_start_3514_);
lean_inc(v_array_3513_);
lean_dec(v_a_3511_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3559_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
uint8_t v___x_3519_; 
v___x_3519_ = lean_nat_dec_lt(v_start_3514_, v_stop_3515_);
if (v___x_3519_ == 0)
{
lean_del_object(v___x_3517_);
lean_dec(v_stop_3515_);
lean_dec(v_start_3514_);
lean_dec_ref(v_array_3513_);
return v_b_3512_;
}
else
{
lean_object* v_fst_3520_; lean_object* v_snd_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3558_; 
v_fst_3520_ = lean_ctor_get(v_b_3512_, 0);
v_snd_3521_ = lean_ctor_get(v_b_3512_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_b_3512_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3523_ = v_b_3512_;
v_isShared_3524_ = v_isSharedCheck_3558_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_snd_3521_);
lean_inc(v_fst_3520_);
lean_dec(v_b_3512_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3558_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v___x_3525_ = lean_unsigned_to_nat(1u);
v___x_3526_ = lean_nat_add(v_start_3514_, v___x_3525_);
lean_inc_ref(v_array_3513_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 1, v___x_3526_);
v___x_3528_ = v___x_3517_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_array_3513_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3526_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_stop_3515_);
v___x_3528_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3554_; 
v___x_3529_ = lean_array_fget(v_array_3513_, v_start_3514_);
lean_dec(v_start_3514_);
lean_dec_ref(v_array_3513_);
v___x_3530_ = lean_unsigned_to_nat(2u);
v___x_3531_ = lean_mk_empty_array_with_capacity(v___x_3530_);
lean_inc(v_fst_3520_);
lean_inc_ref(v___x_3531_);
v___x_3532_ = lean_array_push(v___x_3531_, v_fst_3520_);
v___x_3533_ = lean_array_push(v___x_3532_, v_snd_3521_);
v___x_3534_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3533_);
v___x_3535_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
lean_inc(v___x_3529_);
v___x_3536_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_3529_);
v___x_3537_ = lean_unsigned_to_nat(3u);
v___x_3538_ = lean_mk_empty_array_with_capacity(v___x_3537_);
lean_inc_ref(v___x_3538_);
v___x_3539_ = lean_array_push(v___x_3538_, v_fst_3520_);
v___x_3540_ = lean_array_push(v___x_3539_, v___x_3535_);
lean_inc(v___x_3536_);
v___x_3541_ = lean_array_push(v___x_3540_, v___x_3536_);
v___x_3542_ = l_Lean_Fmt_Doc_join___redArg(v___x_3541_);
v___x_3543_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3544_ = lean_array_push(v___x_3538_, v___x_3534_);
v___x_3545_ = lean_array_push(v___x_3544_, v___x_3543_);
lean_inc_ref(v___x_3545_);
v___x_3546_ = lean_array_push(v___x_3545_, v___x_3536_);
v___x_3547_ = l_Lean_Fmt_Doc_join___redArg(v___x_3546_);
v___x_3548_ = lean_array_push(v___x_3531_, v___x_3542_);
v___x_3549_ = lean_array_push(v___x_3548_, v___x_3547_);
v___x_3550_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3549_);
v___x_3551_ = lean_array_push(v___x_3545_, v___x_3529_);
v___x_3552_ = l_Lean_Fmt_Doc_join___redArg(v___x_3551_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 1, v___x_3552_);
lean_ctor_set(v___x_3523_, 0, v___x_3550_);
v___x_3554_ = v___x_3523_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3556_, 1, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
v_a_3511_ = v___x_3528_;
v_b_3512_ = v___x_3554_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object* v_ds_3560_){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3561_ = lean_array_get_size(v_ds_3560_);
v___x_3562_ = lean_unsigned_to_nat(0u);
v___x_3563_ = lean_nat_dec_eq(v___x_3561_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; lean_object* v_lastNotFlattened_3565_; lean_object* v___x_3566_; uint8_t v___x_3567_; 
v___x_3564_ = lean_box(0);
v_lastNotFlattened_3565_ = lean_array_get(v___x_3564_, v_ds_3560_, v___x_3562_);
v___x_3566_ = lean_unsigned_to_nat(1u);
v___x_3567_ = lean_nat_dec_eq(v___x_3561_, v___x_3566_);
if (v___x_3567_ == 0)
{
lean_object* v_lastFlattened_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v_fst_3572_; lean_object* v_snd_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_inc(v_lastNotFlattened_3565_);
v_lastFlattened_3568_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_3565_);
v___x_3569_ = l_Array_toSubarray___redArg(v_ds_3560_, v___x_3566_, v___x_3561_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_lastFlattened_3568_);
lean_ctor_set(v___x_3570_, 1, v_lastNotFlattened_3565_);
v___x_3571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(v___x_3569_, v___x_3570_);
v_fst_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc(v_fst_3572_);
v_snd_3573_ = lean_ctor_get(v___x_3571_, 1);
lean_inc(v_snd_3573_);
lean_dec_ref(v___x_3571_);
v___x_3574_ = lean_unsigned_to_nat(2u);
v___x_3575_ = lean_mk_empty_array_with_capacity(v___x_3574_);
v___x_3576_ = lean_array_push(v___x_3575_, v_fst_3572_);
v___x_3577_ = lean_array_push(v___x_3576_, v_snd_3573_);
v___x_3578_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3577_);
return v___x_3578_;
}
else
{
lean_dec_ref(v_ds_3560_);
return v_lastNotFlattened_3565_;
}
}
else
{
lean_object* v___x_3579_; 
lean_dec_ref(v_ds_3560_);
v___x_3579_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace(lean_object* v_00_u03c4_3580_, lean_object* v_ds_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_ds_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0(lean_object* v_00_u03c4_3583_, lean_object* v_inst_3584_, lean_object* v_R_3585_, lean_object* v_a_3586_, lean_object* v_b_3587_, lean_object* v_c_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(v_a_3586_, v_b_3587_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(lean_object* v_boundarySep_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_){
_start:
{
lean_object* v_array_3593_; lean_object* v_start_3594_; lean_object* v_stop_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3644_; 
v_array_3593_ = lean_ctor_get(v_a_3591_, 0);
v_start_3594_ = lean_ctor_get(v_a_3591_, 1);
v_stop_3595_ = lean_ctor_get(v_a_3591_, 2);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_a_3591_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3597_ = v_a_3591_;
v_isShared_3598_ = v_isSharedCheck_3644_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_stop_3595_);
lean_inc(v_start_3594_);
lean_inc(v_array_3593_);
lean_dec(v_a_3591_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3644_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
uint8_t v___x_3599_; 
v___x_3599_ = lean_nat_dec_lt(v_start_3594_, v_stop_3595_);
if (v___x_3599_ == 0)
{
lean_del_object(v___x_3597_);
lean_dec(v_stop_3595_);
lean_dec(v_start_3594_);
lean_dec_ref(v_array_3593_);
lean_dec(v_boundarySep_3590_);
return v_b_3592_;
}
else
{
lean_object* v___x_3600_; lean_object* v_fst_3601_; lean_object* v_snd_3602_; lean_object* v_fst_3603_; lean_object* v_snd_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3643_; 
v___x_3600_ = lean_array_fget_borrowed(v_array_3593_, v_start_3594_);
v_fst_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_fst_3601_);
v_snd_3602_ = lean_ctor_get(v___x_3600_, 1);
lean_inc(v_snd_3602_);
v_fst_3603_ = lean_ctor_get(v_b_3592_, 0);
v_snd_3604_ = lean_ctor_get(v_b_3592_, 1);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_b_3592_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3606_ = v_b_3592_;
v_isShared_3607_ = v_isSharedCheck_3643_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_snd_3604_);
lean_inc(v_fst_3603_);
lean_dec(v_b_3592_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3643_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_add(v_start_3594_, v___x_3608_);
lean_dec(v_start_3594_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 1, v___x_3609_);
v___x_3611_ = v___x_3597_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_array_3593_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3642_, 2, v_stop_3595_);
v___x_3611_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___y_3618_; uint8_t v___x_3640_; 
v___x_3612_ = lean_unsigned_to_nat(2u);
v___x_3613_ = lean_mk_empty_array_with_capacity(v___x_3612_);
lean_inc(v_fst_3603_);
lean_inc_ref(v___x_3613_);
v___x_3614_ = lean_array_push(v___x_3613_, v_fst_3603_);
v___x_3615_ = lean_array_push(v___x_3614_, v_snd_3604_);
v___x_3616_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3615_);
v___x_3640_ = lean_unbox(v_snd_3602_);
lean_dec(v_snd_3602_);
if (v___x_3640_ == 0)
{
lean_object* v_sep_3641_; 
v_sep_3641_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
v___y_3618_ = v_sep_3641_;
goto v___jp_3617_;
}
else
{
lean_inc(v_boundarySep_3590_);
v___y_3618_ = v_boundarySep_3590_;
goto v___jp_3617_;
}
v___jp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
lean_inc(v_fst_3601_);
v___x_3619_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_3601_);
v___x_3620_ = lean_unsigned_to_nat(3u);
v___x_3621_ = lean_mk_empty_array_with_capacity(v___x_3620_);
lean_inc_ref(v___x_3621_);
v___x_3622_ = lean_array_push(v___x_3621_, v_fst_3603_);
v___x_3623_ = lean_array_push(v___x_3622_, v___y_3618_);
lean_inc(v___x_3619_);
v___x_3624_ = lean_array_push(v___x_3623_, v___x_3619_);
v___x_3625_ = l_Lean_Fmt_Doc_join___redArg(v___x_3624_);
v___x_3626_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3627_ = lean_array_push(v___x_3621_, v___x_3616_);
v___x_3628_ = lean_array_push(v___x_3627_, v___x_3626_);
lean_inc_ref(v___x_3628_);
v___x_3629_ = lean_array_push(v___x_3628_, v___x_3619_);
v___x_3630_ = l_Lean_Fmt_Doc_join___redArg(v___x_3629_);
v___x_3631_ = lean_array_push(v___x_3613_, v___x_3625_);
v___x_3632_ = lean_array_push(v___x_3631_, v___x_3630_);
v___x_3633_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3632_);
v___x_3634_ = lean_array_push(v___x_3628_, v_fst_3601_);
v___x_3635_ = l_Lean_Fmt_Doc_join___redArg(v___x_3634_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 1, v___x_3635_);
lean_ctor_set(v___x_3606_, 0, v___x_3633_);
v___x_3637_ = v___x_3606_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
v_a_3591_ = v___x_3611_;
v_b_3592_ = v___x_3637_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(size_t v_sz_3645_, size_t v_i_3646_, lean_object* v_bs_3647_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_usize_dec_lt(v_i_3646_, v_sz_3645_);
if (v___x_3648_ == 0)
{
return v_bs_3647_;
}
else
{
lean_object* v_v_3649_; lean_object* v___x_3650_; lean_object* v_bs_x27_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; size_t v___x_3656_; size_t v___x_3657_; lean_object* v___x_3658_; 
v_v_3649_ = lean_array_uget(v_bs_3647_, v_i_3646_);
v___x_3650_ = lean_unsigned_to_nat(0u);
v_bs_x27_3651_ = lean_array_uset(v_bs_3647_, v_i_3646_, v___x_3650_);
v___x_3652_ = lean_usize_to_nat(v_i_3646_);
v___x_3653_ = lean_nat_dec_eq(v___x_3652_, v___x_3650_);
lean_dec(v___x_3652_);
v___x_3654_ = lean_box(v___x_3653_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v_v_3649_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = ((size_t)1ULL);
v___x_3657_ = lean_usize_add(v_i_3646_, v___x_3656_);
v___x_3658_ = lean_array_uset(v_bs_x27_3651_, v_i_3646_, v___x_3655_);
v_i_3646_ = v___x_3657_;
v_bs_3647_ = v___x_3658_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg___boxed(lean_object* v_sz_3660_, lean_object* v_i_3661_, lean_object* v_bs_3662_){
_start:
{
size_t v_sz_boxed_3663_; size_t v_i_boxed_3664_; lean_object* v_res_3665_; 
v_sz_boxed_3663_ = lean_unbox_usize(v_sz_3660_);
lean_dec(v_sz_3660_);
v_i_boxed_3664_ = lean_unbox_usize(v_i_3661_);
lean_dec(v_i_3661_);
v_res_3665_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_boxed_3663_, v_i_boxed_3664_, v_bs_3662_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(lean_object* v_as_3666_, size_t v_i_3667_, size_t v_stop_3668_, lean_object* v_b_3669_){
_start:
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_usize_dec_eq(v_i_3667_, v_stop_3668_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; size_t v_sz_3672_; size_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; size_t v___x_3676_; size_t v___x_3677_; 
v___x_3671_ = lean_array_uget_borrowed(v_as_3666_, v_i_3667_);
v_sz_3672_ = lean_array_size(v___x_3671_);
v___x_3673_ = ((size_t)0ULL);
lean_inc(v___x_3671_);
v___x_3674_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_3672_, v___x_3673_, v___x_3671_);
v___x_3675_ = l_Array_append___redArg(v_b_3669_, v___x_3674_);
lean_dec_ref(v___x_3674_);
v___x_3676_ = ((size_t)1ULL);
v___x_3677_ = lean_usize_add(v_i_3667_, v___x_3676_);
v_i_3667_ = v___x_3677_;
v_b_3669_ = v___x_3675_;
goto _start;
}
else
{
return v_b_3669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg___boxed(lean_object* v_as_3679_, lean_object* v_i_3680_, lean_object* v_stop_3681_, lean_object* v_b_3682_){
_start:
{
size_t v_i_boxed_3683_; size_t v_stop_boxed_3684_; lean_object* v_res_3685_; 
v_i_boxed_3683_ = lean_unbox_usize(v_i_3680_);
lean_dec(v_i_3680_);
v_stop_boxed_3684_ = lean_unbox_usize(v_stop_3681_);
lean_dec(v_stop_3681_);
v_res_3685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_3679_, v_i_boxed_3683_, v_stop_boxed_3684_, v_b_3682_);
lean_dec_ref(v_as_3679_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object* v_boundaryPenalty_3692_, lean_object* v_dss_3693_){
_start:
{
lean_object* v___x_3694_; lean_object* v___y_3696_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3694_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0));
v___x_3725_ = lean_unsigned_to_nat(0u);
v___x_3726_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1));
v___x_3727_ = lean_array_get_size(v_dss_3693_);
v___x_3728_ = lean_nat_dec_lt(v___x_3725_, v___x_3727_);
if (v___x_3728_ == 0)
{
v___y_3696_ = v___x_3726_;
goto v___jp_3695_;
}
else
{
size_t v___x_3729_; size_t v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = lean_usize_of_nat(v___x_3727_);
v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_dss_3693_, v___x_3729_, v___x_3730_, v___x_3726_);
v___y_3696_ = v___x_3731_;
goto v___jp_3695_;
}
v___jp_3695_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3697_ = lean_array_get_size(v___y_3696_);
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = lean_nat_dec_eq(v___x_3697_, v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; lean_object* v_fst_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3722_; 
v___x_3700_ = lean_array_get(v___x_3694_, v___y_3696_, v___x_3698_);
v_fst_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; 
v_unused_3723_ = lean_ctor_get(v___x_3700_, 1);
lean_dec(v_unused_3723_);
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3722_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_fst_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3722_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; uint8_t v___x_3706_; 
v___x_3705_ = lean_unsigned_to_nat(1u);
v___x_3706_ = lean_nat_dec_eq(v___x_3697_, v___x_3705_);
if (v___x_3706_ == 0)
{
lean_object* v_sep_3707_; lean_object* v_boundarySep_3708_; lean_object* v_lastFlattened_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
v_sep_3707_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
v_boundarySep_3708_ = l_Lean_Fmt_Doc_costing___override___redArg(v_boundaryPenalty_3692_, v_sep_3707_);
lean_inc(v_fst_3701_);
v_lastFlattened_3709_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_3701_);
v___x_3710_ = l_Array_toSubarray___redArg(v___y_3696_, v___x_3705_, v___x_3697_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 1, v_fst_3701_);
lean_ctor_set(v___x_3703_, 0, v_lastFlattened_3709_);
v___x_3712_ = v___x_3703_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_lastFlattened_3709_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_fst_3701_);
v___x_3712_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v_fst_3714_; lean_object* v_snd_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3713_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_boundarySep_3708_, v___x_3710_, v___x_3712_);
v_fst_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_fst_3714_);
v_snd_3715_ = lean_ctor_get(v___x_3713_, 1);
lean_inc(v_snd_3715_);
lean_dec_ref(v___x_3713_);
v___x_3716_ = lean_unsigned_to_nat(2u);
v___x_3717_ = lean_mk_empty_array_with_capacity(v___x_3716_);
v___x_3718_ = lean_array_push(v___x_3717_, v_fst_3714_);
v___x_3719_ = lean_array_push(v___x_3718_, v_snd_3715_);
v___x_3720_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3719_);
return v___x_3720_;
}
}
else
{
lean_del_object(v___x_3703_);
lean_dec_ref(v___y_3696_);
lean_dec(v_boundaryPenalty_3692_);
return v_fst_3701_;
}
}
}
else
{
lean_object* v___x_3724_; 
lean_dec_ref(v___y_3696_);
lean_dec(v_boundaryPenalty_3692_);
v___x_3724_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___boxed(lean_object* v_boundaryPenalty_3732_, lean_object* v_dss_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_3732_, v_dss_3733_);
lean_dec_ref(v_dss_3733_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(lean_object* v_00_u03c4_3735_, lean_object* v_boundaryPenalty_3736_, lean_object* v_dss_3737_){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_3736_, v_dss_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___boxed(lean_object* v_00_u03c4_3739_, lean_object* v_boundaryPenalty_3740_, lean_object* v_dss_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(v_00_u03c4_3739_, v_boundaryPenalty_3740_, v_dss_3741_);
lean_dec_ref(v_dss_3741_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(lean_object* v_00_u03c4_3743_, lean_object* v_as_3744_, size_t v_sz_3745_, size_t v_i_3746_, lean_object* v_bs_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_3745_, v_i_3746_, v_bs_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_00_u03c4_3749_, lean_object* v_as_3750_, lean_object* v_sz_3751_, lean_object* v_i_3752_, lean_object* v_bs_3753_){
_start:
{
size_t v_sz_boxed_3754_; size_t v_i_boxed_3755_; lean_object* v_res_3756_; 
v_sz_boxed_3754_ = lean_unbox_usize(v_sz_3751_);
lean_dec(v_sz_3751_);
v_i_boxed_3755_ = lean_unbox_usize(v_i_3752_);
lean_dec(v_i_3752_);
v_res_3756_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(v_00_u03c4_3749_, v_as_3750_, v_sz_boxed_3754_, v_i_boxed_3755_, v_bs_3753_);
lean_dec_ref(v_as_3750_);
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_00_u03c4_3757_, lean_object* v_boundarySep_3758_, lean_object* v_inst_3759_, lean_object* v_R_3760_, lean_object* v_a_3761_, lean_object* v_b_3762_, lean_object* v_c_3763_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_boundarySep_3758_, v_a_3761_, v_b_3762_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(lean_object* v_00_u03c4_3765_, lean_object* v_as_3766_, size_t v_i_3767_, size_t v_stop_3768_, lean_object* v_b_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_3766_, v_i_3767_, v_stop_3768_, v_b_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___boxed(lean_object* v_00_u03c4_3771_, lean_object* v_as_3772_, lean_object* v_i_3773_, lean_object* v_stop_3774_, lean_object* v_b_3775_){
_start:
{
size_t v_i_boxed_3776_; size_t v_stop_boxed_3777_; lean_object* v_res_3778_; 
v_i_boxed_3776_ = lean_unbox_usize(v_i_3773_);
lean_dec(v_i_3773_);
v_stop_boxed_3777_ = lean_unbox_usize(v_stop_3774_);
lean_dec(v_stop_3774_);
v_res_3778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(v_00_u03c4_3771_, v_as_3772_, v_i_boxed_3776_, v_stop_boxed_3777_, v_b_3775_);
lean_dec_ref(v_as_3772_);
return v_res_3778_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3779_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
v___x_3780_ = lean_unsigned_to_nat(2u);
v___x_3781_ = lean_mk_empty_array_with_capacity(v___x_3780_);
v___x_3782_ = lean_array_push(v___x_3781_, v___x_3779_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(lean_object* v_wrap_3783_, lean_object* v_as_3784_, size_t v_sz_3785_, size_t v_i_3786_, lean_object* v_b_3787_){
_start:
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_lt(v_i_3786_, v_sz_3785_);
if (v___x_3788_ == 0)
{
lean_dec_ref(v_wrap_3783_);
return v_b_3787_;
}
else
{
lean_object* v_fst_3789_; lean_object* v_snd_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3826_; 
v_fst_3789_ = lean_ctor_get(v_b_3787_, 0);
v_snd_3790_ = lean_ctor_get(v_b_3787_, 1);
v_isSharedCheck_3826_ = !lean_is_exclusive(v_b_3787_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3792_ = v_b_3787_;
v_isShared_3793_ = v_isSharedCheck_3826_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_snd_3790_);
lean_inc(v_fst_3789_);
lean_dec(v_b_3787_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3826_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_a_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v_a_3794_ = lean_array_uget_borrowed(v_as_3784_, v_i_3786_);
v___x_3795_ = lean_unsigned_to_nat(2u);
v___x_3796_ = lean_mk_empty_array_with_capacity(v___x_3795_);
lean_inc(v_fst_3789_);
lean_inc_ref_n(v___x_3796_, 3);
v___x_3797_ = lean_array_push(v___x_3796_, v_fst_3789_);
v___x_3798_ = lean_array_push(v___x_3797_, v_snd_3790_);
v___x_3799_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3798_);
v___x_3800_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_3801_ = lean_array_push(v___x_3800_, v___x_3799_);
v___x_3802_ = l_Lean_Fmt_Doc_join___redArg(v___x_3801_);
lean_inc_ref_n(v_wrap_3783_, 2);
v___x_3803_ = lean_apply_1(v_wrap_3783_, v___x_3802_);
lean_inc_n(v_a_3794_, 2);
v___x_3804_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_a_3794_);
v___x_3805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_3806_ = lean_array_push(v___x_3805_, v_fst_3789_);
v___x_3807_ = l_Lean_Fmt_Doc_join___redArg(v___x_3806_);
v___x_3808_ = lean_apply_1(v_wrap_3783_, v___x_3807_);
v___x_3809_ = lean_array_push(v___x_3796_, v___x_3804_);
lean_inc_ref(v___x_3809_);
v___x_3810_ = lean_array_push(v___x_3809_, v___x_3808_);
v___x_3811_ = l_Lean_Fmt_Doc_join___redArg(v___x_3810_);
lean_inc(v___x_3803_);
v___x_3812_ = lean_array_push(v___x_3809_, v___x_3803_);
v___x_3813_ = l_Lean_Fmt_Doc_join___redArg(v___x_3812_);
v___x_3814_ = lean_array_push(v___x_3796_, v___x_3811_);
v___x_3815_ = lean_array_push(v___x_3814_, v___x_3813_);
v___x_3816_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3815_);
v___x_3817_ = lean_array_push(v___x_3796_, v_a_3794_);
v___x_3818_ = lean_array_push(v___x_3817_, v___x_3803_);
v___x_3819_ = l_Lean_Fmt_Doc_join___redArg(v___x_3818_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 1, v___x_3819_);
lean_ctor_set(v___x_3792_, 0, v___x_3816_);
v___x_3821_ = v___x_3792_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
size_t v___x_3822_; size_t v___x_3823_; 
v___x_3822_ = ((size_t)1ULL);
v___x_3823_ = lean_usize_add(v_i_3786_, v___x_3822_);
v_i_3786_ = v___x_3823_;
v_b_3787_ = v___x_3821_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___boxed(lean_object* v_wrap_3827_, lean_object* v_as_3828_, lean_object* v_sz_3829_, lean_object* v_i_3830_, lean_object* v_b_3831_){
_start:
{
size_t v_sz_boxed_3832_; size_t v_i_boxed_3833_; lean_object* v_res_3834_; 
v_sz_boxed_3832_ = lean_unbox_usize(v_sz_3829_);
lean_dec(v_sz_3829_);
v_i_boxed_3833_ = lean_unbox_usize(v_i_3830_);
lean_dec(v_i_3830_);
v_res_3834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_3827_, v_as_3828_, v_sz_boxed_3832_, v_i_boxed_3833_, v_b_3831_);
lean_dec_ref(v_as_3828_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object* v_ds_3835_, lean_object* v_wrap_3836_){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3837_ = lean_array_get_size(v_ds_3835_);
v___x_3838_ = lean_unsigned_to_nat(0u);
v___x_3839_ = lean_nat_dec_eq(v___x_3837_, v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v_restNotFlattened_3843_; uint8_t v___x_3844_; 
v___x_3840_ = lean_box(0);
v___x_3841_ = lean_unsigned_to_nat(1u);
v___x_3842_ = lean_nat_sub(v___x_3837_, v___x_3841_);
v_restNotFlattened_3843_ = lean_array_get(v___x_3840_, v_ds_3835_, v___x_3842_);
lean_dec(v___x_3842_);
v___x_3844_ = lean_nat_dec_eq(v___x_3837_, v___x_3841_);
if (v___x_3844_ == 0)
{
lean_object* v_restFlattened_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; size_t v_sz_3849_; size_t v___x_3850_; lean_object* v___x_3851_; lean_object* v_fst_3852_; lean_object* v_snd_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_inc(v_restNotFlattened_3843_);
v_restFlattened_3845_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_3843_);
v___x_3846_ = lean_array_pop(v_ds_3835_);
v___x_3847_ = l_Array_reverse___redArg(v___x_3846_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_restFlattened_3845_);
lean_ctor_set(v___x_3848_, 1, v_restNotFlattened_3843_);
v_sz_3849_ = lean_array_size(v___x_3847_);
v___x_3850_ = ((size_t)0ULL);
v___x_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_3836_, v___x_3847_, v_sz_3849_, v___x_3850_, v___x_3848_);
lean_dec_ref(v___x_3847_);
v_fst_3852_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_fst_3852_);
v_snd_3853_ = lean_ctor_get(v___x_3851_, 1);
lean_inc(v_snd_3853_);
lean_dec_ref(v___x_3851_);
v___x_3854_ = lean_unsigned_to_nat(2u);
v___x_3855_ = lean_mk_empty_array_with_capacity(v___x_3854_);
v___x_3856_ = lean_array_push(v___x_3855_, v_fst_3852_);
v___x_3857_ = lean_array_push(v___x_3856_, v_snd_3853_);
v___x_3858_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3857_);
return v___x_3858_;
}
else
{
lean_dec_ref(v_wrap_3836_);
lean_dec_ref(v_ds_3835_);
return v_restNotFlattened_3843_;
}
}
else
{
lean_object* v___x_3859_; 
lean_dec_ref(v_wrap_3836_);
lean_dec_ref(v_ds_3835_);
v___x_3859_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping(lean_object* v_00_u03c4_3860_, lean_object* v_ds_3861_, lean_object* v_wrap_3862_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_ds_3861_, v_wrap_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0(lean_object* v_00_u03c4_3864_, lean_object* v_wrap_3865_, lean_object* v_as_3866_, size_t v_sz_3867_, size_t v_i_3868_, lean_object* v_b_3869_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_3865_, v_as_3866_, v_sz_3867_, v_i_3868_, v_b_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___boxed(lean_object* v_00_u03c4_3871_, lean_object* v_wrap_3872_, lean_object* v_as_3873_, lean_object* v_sz_3874_, lean_object* v_i_3875_, lean_object* v_b_3876_){
_start:
{
size_t v_sz_boxed_3877_; size_t v_i_boxed_3878_; lean_object* v_res_3879_; 
v_sz_boxed_3877_ = lean_unbox_usize(v_sz_3874_);
lean_dec(v_sz_3874_);
v_i_boxed_3878_ = lean_unbox_usize(v_i_3875_);
lean_dec(v_i_3875_);
v_res_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0(v_00_u03c4_3871_, v_wrap_3872_, v_as_3873_, v_sz_boxed_3877_, v_i_boxed_3878_, v_b_3876_);
lean_dec_ref(v_as_3873_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object* v_inst_3880_){
_start:
{
uint8_t v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = 0;
v___x_3882_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3882_, 0, v_inst_3880_);
lean_ctor_set_uint8(v___x_3882_, sizeof(void*)*1, v___x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default(lean_object* v_00_u03b1_3883_, lean_object* v_inst_3884_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable___redArg(lean_object* v_inst_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable(lean_object* v_a_3888_, lean_object* v_inst_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(size_t v_sz_3891_, size_t v_i_3892_, lean_object* v_bs_3893_){
_start:
{
uint8_t v___x_3894_; 
v___x_3894_ = lean_usize_dec_lt(v_i_3892_, v_sz_3891_);
if (v___x_3894_ == 0)
{
return v_bs_3893_;
}
else
{
lean_object* v_v_3895_; lean_object* v_v_3896_; lean_object* v___x_3897_; lean_object* v_bs_x27_3898_; size_t v___x_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v_v_3895_ = lean_array_uget_borrowed(v_bs_3893_, v_i_3892_);
v_v_3896_ = lean_ctor_get(v_v_3895_, 0);
lean_inc(v_v_3896_);
v___x_3897_ = lean_unsigned_to_nat(0u);
v_bs_x27_3898_ = lean_array_uset(v_bs_3893_, v_i_3892_, v___x_3897_);
v___x_3899_ = ((size_t)1ULL);
v___x_3900_ = lean_usize_add(v_i_3892_, v___x_3899_);
v___x_3901_ = lean_array_uset(v_bs_x27_3898_, v_i_3892_, v_v_3896_);
v_i_3892_ = v___x_3900_;
v_bs_3893_ = v___x_3901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg___boxed(lean_object* v_sz_3903_, lean_object* v_i_3904_, lean_object* v_bs_3905_){
_start:
{
size_t v_sz_boxed_3906_; size_t v_i_boxed_3907_; lean_object* v_res_3908_; 
v_sz_boxed_3906_ = lean_unbox_usize(v_sz_3903_);
lean_dec(v_sz_3903_);
v_i_boxed_3907_ = lean_unbox_usize(v_i_3904_);
lean_dec(v_i_3904_);
v_res_3908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_boxed_3906_, v_i_boxed_3907_, v_bs_3905_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(size_t v_sz_3909_, size_t v_i_3910_, lean_object* v_bs_3911_){
_start:
{
uint8_t v___x_3912_; 
v___x_3912_ = lean_usize_dec_lt(v_i_3910_, v_sz_3909_);
if (v___x_3912_ == 0)
{
return v_bs_3911_;
}
else
{
lean_object* v_v_3913_; lean_object* v___x_3914_; lean_object* v_bs_x27_3915_; size_t v_sz_3916_; size_t v___x_3917_; lean_object* v___x_3918_; size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; 
v_v_3913_ = lean_array_uget(v_bs_3911_, v_i_3910_);
v___x_3914_ = lean_unsigned_to_nat(0u);
v_bs_x27_3915_ = lean_array_uset(v_bs_3911_, v_i_3910_, v___x_3914_);
v_sz_3916_ = lean_array_size(v_v_3913_);
v___x_3917_ = ((size_t)0ULL);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3916_, v___x_3917_, v_v_3913_);
v___x_3919_ = ((size_t)1ULL);
v___x_3920_ = lean_usize_add(v_i_3910_, v___x_3919_);
v___x_3921_ = lean_array_uset(v_bs_x27_3915_, v_i_3910_, v___x_3918_);
v_i_3910_ = v___x_3920_;
v_bs_3911_ = v___x_3921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg___boxed(lean_object* v_sz_3923_, lean_object* v_i_3924_, lean_object* v_bs_3925_){
_start:
{
size_t v_sz_boxed_3926_; size_t v_i_boxed_3927_; lean_object* v_res_3928_; 
v_sz_boxed_3926_ = lean_unbox_usize(v_sz_3923_);
lean_dec(v_sz_3923_);
v_i_boxed_3927_ = lean_unbox_usize(v_i_3924_);
lean_dec(v_i_3924_);
v_res_3928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_boxed_3926_, v_i_boxed_3927_, v_bs_3925_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(lean_object* v_a_3929_, lean_object* v_a_3930_){
_start:
{
if (lean_obj_tag(v_a_3929_) == 0)
{
lean_object* v___x_3931_; 
v___x_3931_ = l_List_reverse___redArg(v_a_3930_);
return v___x_3931_;
}
else
{
lean_object* v_head_3932_; lean_object* v_tail_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3942_; 
v_head_3932_ = lean_ctor_get(v_a_3929_, 0);
v_tail_3933_ = lean_ctor_get(v_a_3929_, 1);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_a_3929_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3935_ = v_a_3929_;
v_isShared_3936_ = v_isSharedCheck_3942_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_tail_3933_);
lean_inc(v_head_3932_);
lean_dec(v_a_3929_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3942_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = lean_array_mk(v_head_3932_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 1, v_a_3930_);
lean_ctor_set(v___x_3935_, 0, v___x_3937_);
v___x_3939_ = v___x_3935_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_a_3930_);
v___x_3939_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
v_a_3929_ = v_tail_3933_;
v_a_3930_ = v___x_3939_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
if (lean_obj_tag(v_a_3943_) == 0)
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3947_, 0, v_a_3944_);
lean_ctor_set(v___x_3947_, 1, v_a_3945_);
v___x_3948_ = l_List_reverse___redArg(v___x_3947_);
v___x_3949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
lean_ctor_set(v___x_3949_, 1, v_a_3946_);
v___x_3950_ = l_List_reverse___redArg(v___x_3949_);
return v___x_3950_;
}
else
{
lean_object* v_head_3951_; lean_object* v_tail_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3968_; 
v_head_3951_ = lean_ctor_get(v_a_3943_, 0);
v_tail_3952_ = lean_ctor_get(v_a_3943_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_a_3943_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3954_ = v_a_3943_;
v_isShared_3955_ = v_isSharedCheck_3968_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_tail_3952_);
lean_inc(v_head_3951_);
lean_dec(v_a_3943_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3968_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
uint8_t v_allowFill_3964_; 
v_allowFill_3964_ = lean_ctor_get_uint8(v_a_3944_, sizeof(void*)*1);
if (v_allowFill_3964_ == 0)
{
goto v___jp_3956_;
}
else
{
uint8_t v_allowFill_3965_; 
v_allowFill_3965_ = lean_ctor_get_uint8(v_head_3951_, sizeof(void*)*1);
if (v_allowFill_3965_ == 0)
{
goto v___jp_3956_;
}
else
{
lean_object* v___x_3966_; 
lean_del_object(v___x_3954_);
v___x_3966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3966_, 0, v_a_3944_);
lean_ctor_set(v___x_3966_, 1, v_a_3945_);
v_a_3943_ = v_tail_3952_;
v_a_3944_ = v_head_3951_;
v_a_3945_ = v___x_3966_;
goto _start;
}
}
v___jp_3956_:
{
lean_object* v___x_3957_; lean_object* v___x_3959_; 
v___x_3957_ = lean_box(0);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 1, v_a_3945_);
lean_ctor_set(v___x_3954_, 0, v_a_3944_);
v___x_3959_ = v___x_3954_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3944_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_a_3945_);
v___x_3959_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = l_List_reverse___redArg(v___x_3959_);
v___x_3961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
lean_ctor_set(v___x_3961_, 1, v_a_3946_);
v_a_3943_ = v_tail_3952_;
v_a_3944_ = v_head_3951_;
v_a_3945_ = v___x_3957_;
v_a_3946_ = v___x_3961_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(lean_object* v_x_3969_){
_start:
{
if (lean_obj_tag(v_x_3969_) == 0)
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_box(0);
return v___x_3970_;
}
else
{
lean_object* v_head_3971_; lean_object* v_tail_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v_head_3971_ = lean_ctor_get(v_x_3969_, 0);
lean_inc(v_head_3971_);
v_tail_3972_ = lean_ctor_get(v_x_3969_, 1);
lean_inc(v_tail_3972_);
lean_dec_ref_known(v_x_3969_, 2);
v___x_3973_ = lean_box(0);
v___x_3974_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_tail_3972_, v_head_3971_, v___x_3973_, v___x_3973_);
return v___x_3974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups___redArg(lean_object* v_ds_3975_){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; size_t v_sz_3981_; size_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3976_ = lean_array_to_list(v_ds_3975_);
v___x_3977_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v___x_3976_);
v___x_3978_ = lean_box(0);
v___x_3979_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v___x_3977_, v___x_3978_);
v___x_3980_ = lean_array_mk(v___x_3979_);
v_sz_3981_ = lean_array_size(v___x_3980_);
v___x_3982_ = ((size_t)0ULL);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_3981_, v___x_3982_, v___x_3980_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups(lean_object* v_00_u03c4_3984_, lean_object* v_ds_3985_){
_start:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3985_);
return v___x_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(lean_object* v_00_u03c4_3987_, size_t v_sz_3988_, size_t v_i_3989_, lean_object* v_bs_3990_){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3988_, v_i_3989_, v_bs_3990_);
return v___x_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___boxed(lean_object* v_00_u03c4_3992_, lean_object* v_sz_3993_, lean_object* v_i_3994_, lean_object* v_bs_3995_){
_start:
{
size_t v_sz_boxed_3996_; size_t v_i_boxed_3997_; lean_object* v_res_3998_; 
v_sz_boxed_3996_ = lean_unbox_usize(v_sz_3993_);
lean_dec(v_sz_3993_);
v_i_boxed_3997_ = lean_unbox_usize(v_i_3994_);
lean_dec(v_i_3994_);
v_res_3998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(v_00_u03c4_3992_, v_sz_boxed_3996_, v_i_boxed_3997_, v_bs_3995_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1(lean_object* v_00_u03c4_3999_, lean_object* v_x_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v_x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2(lean_object* v_00_u03c4_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v_a_4003_, v_a_4004_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(lean_object* v_00_u03c4_4006_, size_t v_sz_4007_, size_t v_i_4008_, lean_object* v_bs_4009_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_4007_, v_i_4008_, v_bs_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___boxed(lean_object* v_00_u03c4_4011_, lean_object* v_sz_4012_, lean_object* v_i_4013_, lean_object* v_bs_4014_){
_start:
{
size_t v_sz_boxed_4015_; size_t v_i_boxed_4016_; lean_object* v_res_4017_; 
v_sz_boxed_4015_ = lean_unbox_usize(v_sz_4012_);
lean_dec(v_sz_4012_);
v_i_boxed_4016_ = lean_unbox_usize(v_i_4013_);
lean_dec(v_i_4013_);
v_res_4017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(v_00_u03c4_4011_, v_sz_boxed_4015_, v_i_boxed_4016_, v_bs_4014_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1(lean_object* v_00_u03c4_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(lean_object* v_sep_4024_, size_t v_sz_4025_, size_t v_i_4026_, lean_object* v_bs_4027_){
_start:
{
uint8_t v___x_4028_; 
v___x_4028_ = lean_usize_dec_lt(v_i_4026_, v_sz_4025_);
if (v___x_4028_ == 0)
{
lean_dec(v_sep_4024_);
return v_bs_4027_;
}
else
{
lean_object* v_v_4029_; lean_object* v___x_4030_; lean_object* v_bs_x27_4031_; lean_object* v___x_4032_; size_t v___x_4033_; size_t v___x_4034_; lean_object* v___x_4035_; 
v_v_4029_ = lean_array_uget(v_bs_4027_, v_i_4026_);
v___x_4030_ = lean_unsigned_to_nat(0u);
v_bs_x27_4031_ = lean_array_uset(v_bs_4027_, v_i_4026_, v___x_4030_);
lean_inc(v_sep_4024_);
v___x_4032_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_4024_, v_v_4029_);
v___x_4033_ = ((size_t)1ULL);
v___x_4034_ = lean_usize_add(v_i_4026_, v___x_4033_);
v___x_4035_ = lean_array_uset(v_bs_x27_4031_, v_i_4026_, v___x_4032_);
v_i_4026_ = v___x_4034_;
v_bs_4027_ = v___x_4035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg___boxed(lean_object* v_sep_4037_, lean_object* v_sz_4038_, lean_object* v_i_4039_, lean_object* v_bs_4040_){
_start:
{
size_t v_sz_boxed_4041_; size_t v_i_boxed_4042_; lean_object* v_res_4043_; 
v_sz_boxed_4041_ = lean_unbox_usize(v_sz_4038_);
lean_dec(v_sz_4038_);
v_i_boxed_4042_ = lean_unbox_usize(v_i_4039_);
lean_dec(v_i_4039_);
v_res_4043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_4037_, v_sz_boxed_4041_, v_i_boxed_4042_, v_bs_4040_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing___redArg(lean_object* v_sep_4044_, lean_object* v_ds_4045_){
_start:
{
lean_object* v_fillGroups_4046_; lean_object* v___x_4047_; size_t v_sz_4048_; size_t v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v_fillGroups_4046_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_4045_);
v___x_4047_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v_sz_4048_ = lean_array_size(v_fillGroups_4046_);
v___x_4049_ = ((size_t)0ULL);
v___x_4050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_4044_, v_sz_4048_, v___x_4049_, v_fillGroups_4046_);
v___x_4051_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_4047_, v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing(lean_object* v_00_u03c4_4052_, lean_object* v_sep_4053_, lean_object* v_ds_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_Fmt_Doc_fillSomeUsing___redArg(v_sep_4053_, v_ds_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0(lean_object* v_00_u03c4_4056_, lean_object* v_sep_4057_, size_t v_sz_4058_, size_t v_i_4059_, lean_object* v_bs_4060_){
_start:
{
lean_object* v___x_4061_; 
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_4057_, v_sz_4058_, v_i_4059_, v_bs_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___boxed(lean_object* v_00_u03c4_4062_, lean_object* v_sep_4063_, lean_object* v_sz_4064_, lean_object* v_i_4065_, lean_object* v_bs_4066_){
_start:
{
size_t v_sz_boxed_4067_; size_t v_i_boxed_4068_; lean_object* v_res_4069_; 
v_sz_boxed_4067_ = lean_unbox_usize(v_sz_4064_);
lean_dec(v_sz_4064_);
v_i_boxed_4068_ = lean_unbox_usize(v_i_4065_);
lean_dec(v_i_4065_);
v_res_4069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0(v_00_u03c4_4062_, v_sep_4063_, v_sz_boxed_4067_, v_i_boxed_4068_, v_bs_4066_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(size_t v_sz_4070_, size_t v_i_4071_, lean_object* v_bs_4072_){
_start:
{
uint8_t v___x_4073_; 
v___x_4073_ = lean_usize_dec_lt(v_i_4071_, v_sz_4070_);
if (v___x_4073_ == 0)
{
return v_bs_4072_;
}
else
{
lean_object* v_v_4074_; lean_object* v___x_4075_; lean_object* v_bs_x27_4076_; lean_object* v___x_4077_; size_t v___x_4078_; size_t v___x_4079_; lean_object* v___x_4080_; 
v_v_4074_ = lean_array_uget(v_bs_4072_, v_i_4071_);
v___x_4075_ = lean_unsigned_to_nat(0u);
v_bs_x27_4076_ = lean_array_uset(v_bs_4072_, v_i_4071_, v___x_4075_);
v___x_4077_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_v_4074_);
v___x_4078_ = ((size_t)1ULL);
v___x_4079_ = lean_usize_add(v_i_4071_, v___x_4078_);
v___x_4080_ = lean_array_uset(v_bs_x27_4076_, v_i_4071_, v___x_4077_);
v_i_4071_ = v___x_4079_;
v_bs_4072_ = v___x_4080_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg___boxed(lean_object* v_sz_4082_, lean_object* v_i_4083_, lean_object* v_bs_4084_){
_start:
{
size_t v_sz_boxed_4085_; size_t v_i_boxed_4086_; lean_object* v_res_4087_; 
v_sz_boxed_4085_ = lean_unbox_usize(v_sz_4082_);
lean_dec(v_sz_4082_);
v_i_boxed_4086_ = lean_unbox_usize(v_i_4083_);
lean_dec(v_i_4083_);
v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_boxed_4085_, v_i_boxed_4086_, v_bs_4084_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object* v_ds_4088_){
_start:
{
lean_object* v_fillGroups_4089_; lean_object* v___x_4090_; size_t v_sz_4091_; size_t v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_fillGroups_4089_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_4088_);
v___x_4090_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v_sz_4091_ = lean_array_size(v_fillGroups_4089_);
v___x_4092_ = ((size_t)0ULL);
v___x_4093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_4091_, v___x_4092_, v_fillGroups_4089_);
v___x_4094_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_4090_, v___x_4093_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace(lean_object* v_00_u03c4_4095_, lean_object* v_ds_4096_){
_start:
{
lean_object* v___x_4097_; 
v___x_4097_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v_ds_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(lean_object* v_00_u03c4_4098_, size_t v_sz_4099_, size_t v_i_4100_, lean_object* v_bs_4101_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_4099_, v_i_4100_, v_bs_4101_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___boxed(lean_object* v_00_u03c4_4103_, lean_object* v_sz_4104_, lean_object* v_i_4105_, lean_object* v_bs_4106_){
_start:
{
size_t v_sz_boxed_4107_; size_t v_i_boxed_4108_; lean_object* v_res_4109_; 
v_sz_boxed_4107_ = lean_unbox_usize(v_sz_4104_);
lean_dec(v_sz_4104_);
v_i_boxed_4108_ = lean_unbox_usize(v_i_4105_);
lean_dec(v_i_4105_);
v_res_4109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(v_00_u03c4_4103_, v_sz_boxed_4107_, v_i_boxed_4108_, v_bs_4106_);
return v_res_4109_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4110_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__0, &l_Lean_Fmt_Doc_nl___closed__0_once, _init_l_Lean_Fmt_Doc_nl___closed__0);
v___x_4111_ = lean_unsigned_to_nat(2u);
v___x_4112_ = lean_mk_empty_array_with_capacity(v___x_4111_);
v___x_4113_ = lean_array_push(v___x_4112_, v___x_4110_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(lean_object* v_wrap_4114_, lean_object* v_as_4115_, size_t v_sz_4116_, size_t v_i_4117_, lean_object* v_b_4118_){
_start:
{
uint8_t v___x_4119_; 
v___x_4119_ = lean_usize_dec_lt(v_i_4117_, v_sz_4116_);
if (v___x_4119_ == 0)
{
lean_dec_ref(v_wrap_4114_);
return v_b_4118_;
}
else
{
lean_object* v_snd_4120_; lean_object* v_fst_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4187_; 
v_snd_4120_ = lean_ctor_get(v_b_4118_, 1);
v_fst_4121_ = lean_ctor_get(v_b_4118_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v_b_4118_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4123_ = v_b_4118_;
v_isShared_4124_ = v_isSharedCheck_4187_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_snd_4120_);
lean_inc(v_fst_4121_);
lean_dec(v_b_4118_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4187_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v_fst_4125_; lean_object* v_snd_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4186_; 
v_fst_4125_ = lean_ctor_get(v_snd_4120_, 0);
v_snd_4126_ = lean_ctor_get(v_snd_4120_, 1);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_snd_4120_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4128_ = v_snd_4120_;
v_isShared_4129_ = v_isSharedCheck_4186_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_snd_4126_);
lean_inc(v_fst_4125_);
lean_dec(v_snd_4120_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4186_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v_a_4130_; lean_object* v_restFlattened_4132_; lean_object* v_restNotFlattened_4133_; lean_object* v_v_4145_; uint8_t v_allowFill_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v_a_4130_ = lean_array_uget_borrowed(v_as_4115_, v_i_4117_);
v_v_4145_ = lean_ctor_get(v_a_4130_, 0);
v_allowFill_4146_ = lean_ctor_get_uint8(v_a_4130_, sizeof(void*)*1);
v___x_4147_ = lean_unsigned_to_nat(2u);
v___x_4148_ = lean_mk_empty_array_with_capacity(v___x_4147_);
lean_inc(v_fst_4121_);
lean_inc_ref(v___x_4148_);
v___x_4149_ = lean_array_push(v___x_4148_, v_fst_4121_);
v___x_4150_ = lean_array_push(v___x_4149_, v_fst_4125_);
v___x_4151_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_4150_);
if (v_allowFill_4146_ == 0)
{
lean_dec(v_snd_4126_);
lean_dec(v_fst_4121_);
goto v___jp_4152_;
}
else
{
uint8_t v___x_4165_; 
v___x_4165_ = lean_unbox(v_snd_4126_);
lean_dec(v_snd_4126_);
if (v___x_4165_ == 0)
{
lean_dec(v_fst_4121_);
goto v___jp_4152_;
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4166_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_4167_ = lean_array_push(v___x_4166_, v___x_4151_);
v___x_4168_ = l_Lean_Fmt_Doc_join___redArg(v___x_4167_);
lean_inc_ref_n(v_wrap_4114_, 2);
v___x_4169_ = lean_apply_1(v_wrap_4114_, v___x_4168_);
lean_inc_n(v_v_4145_, 2);
v___x_4170_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_4145_);
v___x_4171_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_4172_ = lean_array_push(v___x_4171_, v_fst_4121_);
v___x_4173_ = l_Lean_Fmt_Doc_join___redArg(v___x_4172_);
v___x_4174_ = lean_apply_1(v_wrap_4114_, v___x_4173_);
lean_inc_ref_n(v___x_4148_, 2);
v___x_4175_ = lean_array_push(v___x_4148_, v___x_4170_);
lean_inc_ref(v___x_4175_);
v___x_4176_ = lean_array_push(v___x_4175_, v___x_4174_);
v___x_4177_ = l_Lean_Fmt_Doc_join___redArg(v___x_4176_);
lean_inc(v___x_4169_);
v___x_4178_ = lean_array_push(v___x_4175_, v___x_4169_);
v___x_4179_ = l_Lean_Fmt_Doc_join___redArg(v___x_4178_);
v___x_4180_ = lean_array_push(v___x_4148_, v___x_4177_);
v___x_4181_ = lean_array_push(v___x_4180_, v___x_4179_);
v___x_4182_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_4181_);
v___x_4183_ = lean_array_push(v___x_4148_, v_v_4145_);
v___x_4184_ = lean_array_push(v___x_4183_, v___x_4169_);
v___x_4185_ = l_Lean_Fmt_Doc_join___redArg(v___x_4184_);
v_restFlattened_4132_ = v___x_4182_;
v_restNotFlattened_4133_ = v___x_4185_;
goto v___jp_4131_;
}
}
v___jp_4131_:
{
uint8_t v_allowFill_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
v_allowFill_4134_ = lean_ctor_get_uint8(v_a_4130_, sizeof(void*)*1);
v___x_4135_ = lean_box(v_allowFill_4134_);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 1, v___x_4135_);
lean_ctor_set(v___x_4128_, 0, v_restNotFlattened_4133_);
v___x_4137_ = v___x_4128_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_restNotFlattened_4133_);
lean_ctor_set(v_reuseFailAlloc_4144_, 1, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4139_; 
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 1, v___x_4137_);
lean_ctor_set(v___x_4123_, 0, v_restFlattened_4132_);
v___x_4139_ = v___x_4123_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_restFlattened_4132_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
size_t v___x_4140_; size_t v___x_4141_; 
v___x_4140_ = ((size_t)1ULL);
v___x_4141_ = lean_usize_add(v_i_4117_, v___x_4140_);
v_i_4117_ = v___x_4141_;
v_b_4118_ = v___x_4139_;
goto _start;
}
}
}
v___jp_4152_:
{
lean_object* v_v_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_v_4153_ = lean_ctor_get(v_a_4130_, 0);
v___x_4154_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_4155_ = lean_array_push(v___x_4154_, v___x_4151_);
v___x_4156_ = l_Lean_Fmt_Doc_join___redArg(v___x_4155_);
lean_inc_ref(v_wrap_4114_);
v___x_4157_ = lean_apply_1(v_wrap_4114_, v___x_4156_);
lean_inc_n(v_v_4153_, 2);
v___x_4158_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_4153_);
lean_inc_ref(v___x_4148_);
v___x_4159_ = lean_array_push(v___x_4148_, v___x_4158_);
lean_inc(v___x_4157_);
v___x_4160_ = lean_array_push(v___x_4159_, v___x_4157_);
v___x_4161_ = l_Lean_Fmt_Doc_join___redArg(v___x_4160_);
v___x_4162_ = lean_array_push(v___x_4148_, v_v_4153_);
v___x_4163_ = lean_array_push(v___x_4162_, v___x_4157_);
v___x_4164_ = l_Lean_Fmt_Doc_join___redArg(v___x_4163_);
v_restFlattened_4132_ = v___x_4161_;
v_restNotFlattened_4133_ = v___x_4164_;
goto v___jp_4131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___boxed(lean_object* v_wrap_4188_, lean_object* v_as_4189_, lean_object* v_sz_4190_, lean_object* v_i_4191_, lean_object* v_b_4192_){
_start:
{
size_t v_sz_boxed_4193_; size_t v_i_boxed_4194_; lean_object* v_res_4195_; 
v_sz_boxed_4193_ = lean_unbox_usize(v_sz_4190_);
lean_dec(v_sz_4190_);
v_i_boxed_4194_ = lean_unbox_usize(v_i_4191_);
lean_dec(v_i_4191_);
v_res_4195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_4188_, v_as_4189_, v_sz_boxed_4193_, v_i_boxed_4194_, v_b_4192_);
lean_dec_ref(v_as_4189_);
return v_res_4195_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = lean_box(0);
v___x_4197_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object* v_ds_4198_, lean_object* v_wrap_4199_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; 
v___x_4200_ = lean_array_get_size(v_ds_4198_);
v___x_4201_ = lean_unsigned_to_nat(0u);
v___x_4202_ = lean_nat_dec_eq(v___x_4200_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v_last_4206_; uint8_t v___x_4207_; 
v___x_4203_ = lean_obj_once(&l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0, &l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0);
v___x_4204_ = lean_unsigned_to_nat(1u);
v___x_4205_ = lean_nat_sub(v___x_4200_, v___x_4204_);
v_last_4206_ = lean_array_get_borrowed(v___x_4203_, v_ds_4198_, v___x_4205_);
lean_dec(v___x_4205_);
v___x_4207_ = lean_nat_dec_eq(v___x_4200_, v___x_4204_);
if (v___x_4207_ == 0)
{
lean_object* v_v_4208_; uint8_t v_allowFill_4209_; lean_object* v_restFlattened_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; size_t v_sz_4216_; size_t v___x_4217_; lean_object* v___x_4218_; lean_object* v_snd_4219_; lean_object* v_fst_4220_; lean_object* v_fst_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v_v_4208_ = lean_ctor_get(v_last_4206_, 0);
lean_inc_n(v_v_4208_, 2);
v_allowFill_4209_ = lean_ctor_get_uint8(v_last_4206_, sizeof(void*)*1);
v_restFlattened_4210_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_4208_);
v___x_4211_ = lean_array_pop(v_ds_4198_);
v___x_4212_ = l_Array_reverse___redArg(v___x_4211_);
v___x_4213_ = lean_box(v_allowFill_4209_);
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v_v_4208_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v_restFlattened_4210_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v_sz_4216_ = lean_array_size(v___x_4212_);
v___x_4217_ = ((size_t)0ULL);
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_4199_, v___x_4212_, v_sz_4216_, v___x_4217_, v___x_4215_);
lean_dec_ref(v___x_4212_);
v_snd_4219_ = lean_ctor_get(v___x_4218_, 1);
lean_inc(v_snd_4219_);
v_fst_4220_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_fst_4220_);
lean_dec_ref(v___x_4218_);
v_fst_4221_ = lean_ctor_get(v_snd_4219_, 0);
lean_inc(v_fst_4221_);
lean_dec(v_snd_4219_);
v___x_4222_ = lean_unsigned_to_nat(2u);
v___x_4223_ = lean_mk_empty_array_with_capacity(v___x_4222_);
v___x_4224_ = lean_array_push(v___x_4223_, v_fst_4220_);
v___x_4225_ = lean_array_push(v___x_4224_, v_fst_4221_);
v___x_4226_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_4225_);
return v___x_4226_;
}
else
{
lean_object* v_v_4227_; 
lean_inc(v_last_4206_);
lean_dec_ref(v_wrap_4199_);
lean_dec_ref(v_ds_4198_);
v_v_4227_ = lean_ctor_get(v_last_4206_, 0);
lean_inc(v_v_4227_);
lean_dec(v_last_4206_);
return v_v_4227_;
}
}
else
{
lean_object* v___x_4228_; 
lean_dec_ref(v_wrap_4199_);
lean_dec_ref(v_ds_4198_);
v___x_4228_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__0, &l_Lean_Fmt_Doc_empty___closed__0_once, _init_l_Lean_Fmt_Doc_empty___closed__0);
return v___x_4228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping(lean_object* v_00_u03c4_4229_, lean_object* v_ds_4230_, lean_object* v_wrap_4231_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_4230_, v_wrap_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0(lean_object* v_00_u03c4_4233_, lean_object* v_wrap_4234_, lean_object* v_as_4235_, size_t v_sz_4236_, size_t v_i_4237_, lean_object* v_b_4238_){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_4234_, v_as_4235_, v_sz_4236_, v_i_4237_, v_b_4238_);
return v___x_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___boxed(lean_object* v_00_u03c4_4240_, lean_object* v_wrap_4241_, lean_object* v_as_4242_, lean_object* v_sz_4243_, lean_object* v_i_4244_, lean_object* v_b_4245_){
_start:
{
size_t v_sz_boxed_4246_; size_t v_i_boxed_4247_; lean_object* v_res_4248_; 
v_sz_boxed_4246_ = lean_unbox_usize(v_sz_4243_);
lean_dec(v_sz_4243_);
v_i_boxed_4247_ = lean_unbox_usize(v_i_4244_);
lean_dec(v_i_4244_);
v_res_4248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0(v_00_u03c4_4240_, v_wrap_4241_, v_as_4242_, v_sz_boxed_4246_, v_i_boxed_4247_, v_b_4245_);
lean_dec_ref(v_as_4242_);
return v_res_4248_;
}
}
static size_t _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_4249_; size_t v___x_4250_; 
v___x_4249_ = lean_unsigned_to_nat(0u);
v___x_4250_ = lean_usize_of_nat(v___x_4249_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default___redArg(lean_object* v_inst_4251_){
_start:
{
size_t v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_usize_once(&l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0);
v___x_4253_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_4253_, 0, v_inst_4251_);
lean_ctor_set_usize(v___x_4253_, 1, v___x_4252_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default(lean_object* v_00_u03b1_4254_, lean_object* v_inst_4255_){
_start:
{
lean_object* v___x_4256_; 
v___x_4256_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey___redArg(lean_object* v_inst_4257_){
_start:
{
lean_object* v___x_4258_; 
v___x_4258_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_4257_);
return v___x_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey(lean_object* v_a_4259_, lean_object* v_inst_4260_){
_start:
{
lean_object* v___x_4261_; 
v___x_4261_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_4260_);
return v___x_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object* v_v_4262_){
_start:
{
size_t v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = lean_ptr_addr(v_v_4262_);
v___x_4264_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_4264_, 0, v_v_4262_);
lean_ctor_set_usize(v___x_4264_, 1, v___x_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey(lean_object* v_00_u03b1_4265_, lean_object* v_v_4266_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_4266_);
return v___x_4267_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(lean_object* v_v1_4268_, lean_object* v_v2_4269_){
_start:
{
size_t v_ptr_4270_; size_t v_ptr_4271_; uint8_t v___x_4272_; 
v_ptr_4270_ = lean_ctor_get_usize(v_v1_4268_, 1);
v_ptr_4271_ = lean_ctor_get_usize(v_v2_4269_, 1);
v___x_4272_ = lean_usize_dec_eq(v_ptr_4270_, v_ptr_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___lam__0___boxed(lean_object* v_v1_4273_, lean_object* v_v2_4274_){
_start:
{
uint8_t v_res_4275_; lean_object* v_r_4276_; 
v_res_4275_ = l_Lean_Fmt_instBEqPtrKey___redArg___lam__0(v_v1_4273_, v_v2_4274_);
lean_dec_ref(v_v2_4274_);
lean_dec_ref(v_v1_4273_);
v_r_4276_ = lean_box(v_res_4275_);
return v_r_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg(){
_start:
{
lean_object* v___f_4279_; 
v___f_4279_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___redArg___closed__0));
return v___f_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___redArg___boxed(lean_object* v___dummy_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Fmt_instBEqPtrKey___redArg();
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object* v_00_u03b1_4282_){
_start:
{
lean_object* v___f_4283_; 
v___f_4283_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___redArg___closed__0));
return v___f_4283_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(lean_object* v_v_4284_){
_start:
{
size_t v_ptr_4285_; uint64_t v___x_4286_; 
v_ptr_4285_ = lean_ctor_get_usize(v_v_4284_, 1);
v___x_4286_ = lean_usize_to_uint64(v_ptr_4285_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___lam__0___boxed(lean_object* v_v_4287_){
_start:
{
uint64_t v_res_4288_; lean_object* v_r_4289_; 
v_res_4288_ = l_Lean_Fmt_instHashablePtrKey___redArg___lam__0(v_v_4287_);
lean_dec_ref(v_v_4287_);
v_r_4289_ = lean_box_uint64(v_res_4288_);
return v_r_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg(){
_start:
{
lean_object* v___f_4292_; 
v___f_4292_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___redArg___closed__0));
return v___f_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___redArg___boxed(lean_object* v___dummy_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Fmt_instHashablePtrKey___redArg();
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey(lean_object* v_00_u03b1_4295_){
_start:
{
lean_object* v___f_4296_; 
v___f_4296_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___redArg___closed__0));
return v___f_4296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(lean_object* v_x_4297_, lean_object* v_x_4298_){
_start:
{
lean_object* v_aPtr_4299_; lean_object* v_aPtr_4300_; lean_object* v_bPtr_4301_; lean_object* v_bPtr_4302_; size_t v_ptr_4303_; size_t v_ptr_4304_; uint8_t v___x_4305_; 
v_aPtr_4299_ = lean_ctor_get(v_x_4297_, 0);
v_aPtr_4300_ = lean_ctor_get(v_x_4298_, 0);
v_bPtr_4301_ = lean_ctor_get(v_x_4297_, 1);
v_bPtr_4302_ = lean_ctor_get(v_x_4298_, 1);
v_ptr_4303_ = lean_ctor_get_usize(v_aPtr_4299_, 1);
v_ptr_4304_ = lean_ctor_get_usize(v_aPtr_4300_, 1);
v___x_4305_ = lean_usize_dec_eq(v_ptr_4303_, v_ptr_4304_);
if (v___x_4305_ == 0)
{
return v___x_4305_;
}
else
{
size_t v_ptr_4306_; size_t v_ptr_4307_; uint8_t v___x_4308_; 
v_ptr_4306_ = lean_ctor_get_usize(v_bPtr_4301_, 1);
v_ptr_4307_ = lean_ctor_get_usize(v_bPtr_4302_, 1);
v___x_4308_ = lean_usize_dec_eq(v_ptr_4306_, v_ptr_4307_);
return v___x_4308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg___boxed(lean_object* v_x_4309_, lean_object* v_x_4310_){
_start:
{
uint8_t v_res_4311_; lean_object* v_r_4312_; 
v_res_4311_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_4309_, v_x_4310_);
lean_dec_ref(v_x_4310_);
lean_dec_ref(v_x_4309_);
v_r_4312_ = lean_box(v_res_4311_);
return v_r_4312_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq(lean_object* v_00_u03c4_4313_, lean_object* v_inst_4314_, lean_object* v_x_4315_, lean_object* v_x_4316_){
_start:
{
uint8_t v___x_4317_; 
v___x_4317_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_4315_, v_x_4316_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed(lean_object* v_00_u03c4_4318_, lean_object* v_inst_4319_, lean_object* v_x_4320_, lean_object* v_x_4321_){
_start:
{
uint8_t v_res_4322_; lean_object* v_r_4323_; 
v_res_4322_ = l_Lean_Fmt_instBEqBEqCacheKey_beq(v_00_u03c4_4318_, v_inst_4319_, v_x_4320_, v_x_4321_);
lean_dec_ref(v_x_4321_);
lean_dec_ref(v_x_4320_);
lean_dec_ref(v_inst_4319_);
v_r_4323_ = lean_box(v_res_4322_);
return v_r_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey___redArg(lean_object* v_inst_4324_){
_start:
{
lean_object* v___x_4325_; 
v___x_4325_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4325_, 0, lean_box(0));
lean_closure_set(v___x_4325_, 1, v_inst_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey(lean_object* v_00_u03c4_4326_, lean_object* v_inst_4327_){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4328_, 0, lean_box(0));
lean_closure_set(v___x_4328_, 1, v_inst_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(lean_object* v_x_4329_){
_start:
{
lean_object* v_aPtr_4330_; lean_object* v_bPtr_4331_; size_t v_ptr_4332_; size_t v_ptr_4333_; uint64_t v___x_4334_; uint64_t v___x_4335_; uint64_t v___x_4336_; uint64_t v___x_4337_; uint64_t v___x_4338_; 
v_aPtr_4330_ = lean_ctor_get(v_x_4329_, 0);
v_bPtr_4331_ = lean_ctor_get(v_x_4329_, 1);
v_ptr_4332_ = lean_ctor_get_usize(v_aPtr_4330_, 1);
v_ptr_4333_ = lean_ctor_get_usize(v_bPtr_4331_, 1);
v___x_4334_ = 0ULL;
v___x_4335_ = lean_usize_to_uint64(v_ptr_4332_);
v___x_4336_ = lean_uint64_mix_hash(v___x_4334_, v___x_4335_);
v___x_4337_ = lean_usize_to_uint64(v_ptr_4333_);
v___x_4338_ = lean_uint64_mix_hash(v___x_4336_, v___x_4337_);
return v___x_4338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg___boxed(lean_object* v_x_4339_){
_start:
{
uint64_t v_res_4340_; lean_object* v_r_4341_; 
v_res_4340_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_4339_);
lean_dec_ref(v_x_4339_);
v_r_4341_ = lean_box_uint64(v_res_4340_);
return v_r_4341_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash(lean_object* v_00_u03c4_4342_, lean_object* v_inst_4343_, lean_object* v_x_4344_){
_start:
{
uint64_t v___x_4345_; 
v___x_4345_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed(lean_object* v_00_u03c4_4346_, lean_object* v_inst_4347_, lean_object* v_x_4348_){
_start:
{
uint64_t v_res_4349_; lean_object* v_r_4350_; 
v_res_4349_ = l_Lean_Fmt_instHashableBEqCacheKey_hash(v_00_u03c4_4346_, v_inst_4347_, v_x_4348_);
lean_dec_ref(v_x_4348_);
lean_dec_ref(v_inst_4347_);
v_r_4350_ = lean_box_uint64(v_res_4349_);
return v_r_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey___redArg(lean_object* v_inst_4351_){
_start:
{
lean_object* v___x_4352_; 
v___x_4352_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4352_, 0, lean_box(0));
lean_closure_set(v___x_4352_, 1, v_inst_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey(lean_object* v_00_u03c4_4353_, lean_object* v_inst_4354_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4355_, 0, lean_box(0));
lean_closure_set(v___x_4355_, 1, v_inst_4354_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1___redArg(lean_object* v_a_4356_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1(lean_object* v_00_u03c4_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4___redArg(lean_object* v_b_4361_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4361_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4(lean_object* v_00_u03c4_4363_, lean_object* v_b_4364_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4364_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(lean_object* v_inst_4366_, lean_object* v_inst_4367_, lean_object* v_a_4368_, lean_object* v_b_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v___y_4376_; lean_object* v_da1_4381_; lean_object* v_da2_4382_; lean_object* v_db1_4383_; lean_object* v_db2_4384_; lean_object* v___y_4385_; lean_object* v_sa_4392_; lean_object* v_sb_4393_; lean_object* v___y_4394_; 
switch(lean_obj_tag(v_a_4368_))
{
case 0:
{
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
if (lean_obj_tag(v_b_4369_) == 0)
{
uint8_t v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = 1;
v___x_4399_ = lean_box(v___x_4398_);
v___x_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
lean_ctor_set(v___x_4400_, 1, v_a_4370_);
return v___x_4400_;
}
else
{
lean_dec(v_b_4369_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 1:
{
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
if (lean_obj_tag(v_b_4369_) == 1)
{
lean_object* v_f_4401_; lean_object* v_f_4402_; 
v_f_4401_ = lean_ctor_get(v_a_4368_, 1);
lean_inc_ref(v_f_4401_);
lean_dec_ref_known(v_a_4368_, 2);
v_f_4402_ = lean_ctor_get(v_b_4369_, 1);
lean_inc_ref(v_f_4402_);
lean_dec_ref_known(v_b_4369_, 2);
v_sa_4392_ = v_f_4401_;
v_sb_4393_ = v_f_4402_;
v___y_4394_ = v_a_4370_;
goto v___jp_4391_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 2:
{
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
if (lean_obj_tag(v_b_4369_) == 2)
{
lean_object* v_s_4403_; lean_object* v_s_4404_; 
v_s_4403_ = lean_ctor_get(v_a_4368_, 1);
lean_inc_ref(v_s_4403_);
lean_dec_ref_known(v_a_4368_, 2);
v_s_4404_ = lean_ctor_get(v_b_4369_, 1);
lean_inc_ref(v_s_4404_);
lean_dec_ref_known(v_b_4369_, 2);
v_sa_4392_ = v_s_4403_;
v_sb_4393_ = v_s_4404_;
v___y_4394_ = v_a_4370_;
goto v___jp_4391_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 3:
{
if (lean_obj_tag(v_b_4369_) == 3)
{
lean_object* v_id_4405_; lean_object* v_d_4406_; lean_object* v_id_4407_; lean_object* v_d_4408_; uint8_t v___x_4409_; 
v_id_4405_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_id_4405_);
v_d_4406_ = lean_ctor_get(v_a_4368_, 2);
lean_inc(v_d_4406_);
lean_dec_ref_known(v_a_4368_, 3);
v_id_4407_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_id_4407_);
v_d_4408_ = lean_ctor_get(v_b_4369_, 2);
lean_inc(v_d_4408_);
lean_dec_ref_known(v_b_4369_, 3);
v___x_4409_ = lean_nat_dec_eq(v_id_4405_, v_id_4407_);
lean_dec(v_id_4407_);
lean_dec(v_id_4405_);
if (v___x_4409_ == 0)
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec(v_d_4408_);
lean_dec(v_d_4406_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___x_4410_ = lean_box(v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
lean_ctor_set(v___x_4411_, 1, v_a_4370_);
return v___x_4411_;
}
else
{
lean_object* v___x_4412_; 
v___x_4412_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4406_, v_d_4408_, v_a_4370_);
return v___x_4412_;
}
}
else
{
lean_dec_ref_known(v_a_4368_, 3);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 4:
{
if (lean_obj_tag(v_b_4369_) == 4)
{
lean_object* v_d_4413_; lean_object* v_d_4414_; lean_object* v___x_4415_; 
v_d_4413_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4413_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4414_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4414_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4415_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4413_, v_d_4414_, v_a_4370_);
return v___x_4415_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 5:
{
if (lean_obj_tag(v_b_4369_) == 5)
{
lean_object* v_d_4416_; lean_object* v_d_4417_; lean_object* v___x_4418_; 
v_d_4416_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4416_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4417_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4417_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4418_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4416_, v_d_4417_, v_a_4370_);
return v___x_4418_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 6:
{
if (lean_obj_tag(v_b_4369_) == 6)
{
lean_object* v_n_4419_; uint8_t v_isCumulative_4420_; lean_object* v_d_4421_; lean_object* v_n_4422_; uint8_t v_isCumulative_4423_; lean_object* v_d_4424_; uint8_t v___y_4426_; uint8_t v___x_4428_; 
v_n_4419_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_n_4419_);
v_isCumulative_4420_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*3 + 7);
v_d_4421_ = lean_ctor_get(v_a_4368_, 2);
lean_inc(v_d_4421_);
lean_dec_ref_known(v_a_4368_, 3);
v_n_4422_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_n_4422_);
v_isCumulative_4423_ = lean_ctor_get_uint8(v_b_4369_, sizeof(void*)*3 + 7);
v_d_4424_ = lean_ctor_get(v_b_4369_, 2);
lean_inc(v_d_4424_);
lean_dec_ref_known(v_b_4369_, 3);
v___x_4428_ = lean_nat_dec_eq(v_n_4419_, v_n_4422_);
lean_dec(v_n_4422_);
lean_dec(v_n_4419_);
if (v___x_4428_ == 0)
{
lean_dec(v_d_4424_);
lean_dec(v_d_4421_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
goto v___jp_4371_;
}
else
{
if (v_isCumulative_4423_ == 0)
{
if (v_isCumulative_4420_ == 0)
{
v___y_4426_ = v___x_4428_;
goto v___jp_4425_;
}
else
{
lean_dec(v_d_4424_);
lean_dec(v_d_4421_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
goto v___jp_4371_;
}
}
else
{
v___y_4426_ = v_isCumulative_4420_;
goto v___jp_4425_;
}
}
v___jp_4425_:
{
if (v___y_4426_ == 0)
{
lean_dec(v_d_4424_);
lean_dec(v_d_4421_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
goto v___jp_4371_;
}
else
{
lean_object* v___x_4427_; 
v___x_4427_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4421_, v_d_4424_, v_a_4370_);
return v___x_4427_;
}
}
}
else
{
lean_dec_ref_known(v_a_4368_, 3);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 7:
{
if (lean_obj_tag(v_b_4369_) == 7)
{
lean_object* v_d_4429_; lean_object* v_d_4430_; lean_object* v___x_4431_; 
v_d_4429_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4429_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4430_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4430_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4431_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4429_, v_d_4430_, v_a_4370_);
return v___x_4431_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 8:
{
if (lean_obj_tag(v_b_4369_) == 8)
{
uint8_t v_onlyNonCumulative_4432_; 
v_onlyNonCumulative_4432_ = lean_ctor_get_uint8(v_b_4369_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_4432_ == 0)
{
uint8_t v_onlyNonCumulative_4433_; 
v_onlyNonCumulative_4433_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_4433_ == 0)
{
lean_object* v_d_4434_; lean_object* v_d_4435_; lean_object* v___x_4436_; 
v_d_4434_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4434_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4435_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4435_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4436_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4434_, v_d_4435_, v_a_4370_);
return v___x_4436_;
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_dec_ref_known(v_b_4369_, 2);
lean_dec_ref_known(v_a_4368_, 2);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___x_4437_ = lean_box(v_onlyNonCumulative_4432_);
v___x_4438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4437_);
lean_ctor_set(v___x_4438_, 1, v_a_4370_);
return v___x_4438_;
}
}
else
{
uint8_t v_onlyNonCumulative_4439_; 
v_onlyNonCumulative_4439_ = lean_ctor_get_uint8(v_a_4368_, sizeof(void*)*2 + 7);
if (v_onlyNonCumulative_4439_ == 0)
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
lean_dec_ref_known(v_b_4369_, 2);
lean_dec_ref_known(v_a_4368_, 2);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___x_4440_ = lean_box(v_onlyNonCumulative_4439_);
v___x_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4440_);
lean_ctor_set(v___x_4441_, 1, v_a_4370_);
return v___x_4441_;
}
else
{
lean_object* v_d_4442_; lean_object* v_d_4443_; lean_object* v___x_4444_; 
v_d_4442_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4442_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4443_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4443_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4444_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4442_, v_d_4443_, v_a_4370_);
return v___x_4444_;
}
}
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 9:
{
if (lean_obj_tag(v_b_4369_) == 9)
{
lean_object* v_d_4445_; lean_object* v_d_4446_; lean_object* v___x_4447_; 
v_d_4445_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4445_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4446_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4446_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4447_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4445_, v_d_4446_, v_a_4370_);
return v___x_4447_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 10:
{
if (lean_obj_tag(v_b_4369_) == 10)
{
lean_object* v_d_4448_; lean_object* v_d_4449_; lean_object* v___x_4450_; 
v_d_4448_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4448_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4449_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4449_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4450_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4448_, v_d_4449_, v_a_4370_);
return v___x_4450_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 11:
{
if (lean_obj_tag(v_b_4369_) == 11)
{
lean_object* v_d_4451_; lean_object* v_d_4452_; lean_object* v___x_4453_; 
v_d_4451_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_d_4451_);
lean_dec_ref_known(v_a_4368_, 2);
v_d_4452_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_d_4452_);
lean_dec_ref_known(v_b_4369_, 2);
v___x_4453_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4451_, v_d_4452_, v_a_4370_);
return v___x_4453_;
}
else
{
lean_dec_ref_known(v_a_4368_, 2);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 12:
{
if (lean_obj_tag(v_b_4369_) == 12)
{
lean_object* v_p_4454_; lean_object* v_p_4455_; lean_object* v_d_4456_; lean_object* v_d_4457_; lean_object* v_id_4458_; lean_object* v_id_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4469_; 
v_p_4454_ = lean_ctor_get(v_a_4368_, 1);
lean_inc_ref(v_p_4454_);
v_p_4455_ = lean_ctor_get(v_b_4369_, 1);
lean_inc_ref(v_p_4455_);
v_d_4456_ = lean_ctor_get(v_a_4368_, 2);
lean_inc(v_d_4456_);
lean_dec_ref_known(v_a_4368_, 3);
v_d_4457_ = lean_ctor_get(v_b_4369_, 2);
lean_inc(v_d_4457_);
lean_dec_ref_known(v_b_4369_, 3);
v_id_4458_ = lean_ctor_get(v_p_4454_, 1);
lean_inc(v_id_4458_);
lean_dec_ref(v_p_4454_);
v_id_4459_ = lean_ctor_get(v_p_4455_, 1);
v_isSharedCheck_4469_ = !lean_is_exclusive(v_p_4455_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; 
v_unused_4470_ = lean_ctor_get(v_p_4455_, 0);
lean_dec(v_unused_4470_);
v___x_4461_ = v_p_4455_;
v_isShared_4462_ = v_isSharedCheck_4469_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_id_4459_);
lean_dec(v_p_4455_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4469_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
uint8_t v___x_4463_; 
v___x_4463_ = lean_name_eq(v_id_4458_, v_id_4459_);
lean_dec(v_id_4459_);
lean_dec(v_id_4458_);
if (v___x_4463_ == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4466_; 
lean_dec(v_d_4457_);
lean_dec(v_d_4456_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___x_4464_ = lean_box(v___x_4463_);
if (v_isShared_4462_ == 0)
{
lean_ctor_set(v___x_4461_, 1, v_a_4370_);
lean_ctor_set(v___x_4461_, 0, v___x_4464_);
v___x_4466_ = v___x_4461_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
lean_ctor_set(v_reuseFailAlloc_4467_, 1, v_a_4370_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
else
{
lean_object* v___x_4468_; 
lean_del_object(v___x_4461_);
v___x_4468_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4456_, v_d_4457_, v_a_4370_);
return v___x_4468_;
}
}
}
else
{
lean_dec_ref_known(v_a_4368_, 3);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 13:
{
if (lean_obj_tag(v_b_4369_) == 13)
{
lean_object* v_cost_4471_; lean_object* v_d_4472_; lean_object* v_cost_4473_; lean_object* v_d_4474_; lean_object* v___x_4475_; uint8_t v___x_4476_; 
v_cost_4471_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_cost_4471_);
v_d_4472_ = lean_ctor_get(v_a_4368_, 2);
lean_inc(v_d_4472_);
lean_dec_ref_known(v_a_4368_, 3);
v_cost_4473_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_cost_4473_);
v_d_4474_ = lean_ctor_get(v_b_4369_, 2);
lean_inc(v_d_4474_);
lean_dec_ref_known(v_b_4369_, 3);
lean_inc_ref(v_inst_4366_);
v___x_4475_ = lean_apply_2(v_inst_4366_, v_cost_4471_, v_cost_4473_);
v___x_4476_ = lean_unbox(v___x_4475_);
if (v___x_4476_ == 0)
{
lean_object* v___x_4477_; 
lean_dec(v_d_4474_);
lean_dec(v_d_4472_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___x_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4475_);
lean_ctor_set(v___x_4477_, 1, v_a_4370_);
return v___x_4477_;
}
else
{
lean_object* v___x_4478_; 
v___x_4478_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_d_4472_, v_d_4474_, v_a_4370_);
return v___x_4478_;
}
}
else
{
lean_dec_ref_known(v_a_4368_, 3);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
case 14:
{
if (lean_obj_tag(v_b_4369_) == 14)
{
lean_object* v_a_4479_; lean_object* v_b_4480_; lean_object* v_a_4481_; lean_object* v_b_4482_; 
v_a_4479_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_a_4479_);
v_b_4480_ = lean_ctor_get(v_a_4368_, 2);
lean_inc(v_b_4480_);
lean_dec_ref_known(v_a_4368_, 3);
v_a_4481_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_a_4481_);
v_b_4482_ = lean_ctor_get(v_b_4369_, 2);
lean_inc(v_b_4482_);
lean_dec_ref_known(v_b_4369_, 3);
v_da1_4381_ = v_a_4479_;
v_da2_4382_ = v_b_4480_;
v_db1_4383_ = v_a_4481_;
v_db2_4384_ = v_b_4482_;
v___y_4385_ = v_a_4370_;
goto v___jp_4380_;
}
else
{
lean_dec_ref_known(v_a_4368_, 3);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
default: 
{
if (lean_obj_tag(v_b_4369_) == 15)
{
lean_object* v_a_4483_; lean_object* v_b_4484_; lean_object* v_a_4485_; lean_object* v_b_4486_; 
v_a_4483_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_a_4483_);
v_b_4484_ = lean_ctor_get(v_a_4368_, 2);
lean_inc(v_b_4484_);
lean_dec_ref_known(v_a_4368_, 3);
v_a_4485_ = lean_ctor_get(v_b_4369_, 1);
lean_inc(v_a_4485_);
v_b_4486_ = lean_ctor_get(v_b_4369_, 2);
lean_inc(v_b_4486_);
lean_dec_ref_known(v_b_4369_, 3);
v_da1_4381_ = v_a_4483_;
v_da2_4382_ = v_b_4484_;
v_db1_4383_ = v_a_4485_;
v_db2_4384_ = v_b_4486_;
v___y_4385_ = v_a_4370_;
goto v___jp_4380_;
}
else
{
lean_dec_ref_known(v_a_4368_, 3);
lean_dec(v_b_4369_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
v___y_4376_ = v_a_4370_;
goto v___jp_4375_;
}
}
}
v___jp_4371_:
{
uint8_t v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = 0;
v___x_4373_ = lean_box(v___x_4372_);
v___x_4374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
lean_ctor_set(v___x_4374_, 1, v_a_4370_);
return v___x_4374_;
}
v___jp_4375_:
{
uint8_t v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4377_ = 0;
v___x_4378_ = lean_box(v___x_4377_);
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4378_);
lean_ctor_set(v___x_4379_, 1, v___y_4376_);
return v___x_4379_;
}
v___jp_4380_:
{
lean_object* v___x_4386_; lean_object* v_fst_4387_; uint8_t v___x_4388_; 
lean_inc_ref(v_inst_4367_);
lean_inc_ref(v_inst_4366_);
v___x_4386_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_da1_4381_, v_db1_4383_, v___y_4385_);
v_fst_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_fst_4387_);
v___x_4388_ = lean_unbox(v_fst_4387_);
lean_dec(v_fst_4387_);
if (v___x_4388_ == 0)
{
lean_dec(v_db2_4384_);
lean_dec(v_da2_4382_);
lean_dec_ref(v_inst_4367_);
lean_dec_ref(v_inst_4366_);
return v___x_4386_;
}
else
{
lean_object* v_snd_4389_; lean_object* v___x_4390_; 
v_snd_4389_ = lean_ctor_get(v___x_4386_, 1);
lean_inc(v_snd_4389_);
lean_dec_ref(v___x_4386_);
v___x_4390_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4366_, v_inst_4367_, v_da2_4382_, v_db2_4384_, v_snd_4389_);
return v___x_4390_;
}
}
v___jp_4391_:
{
uint8_t v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4395_ = lean_string_dec_eq(v_sa_4392_, v_sb_4393_);
lean_dec_ref(v_sb_4393_);
lean_dec_ref(v_sa_4392_);
v___x_4396_ = lean_box(v___x_4395_);
v___x_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___y_4394_);
return v___x_4397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(lean_object* v_inst_4487_, lean_object* v_inst_4488_, lean_object* v_a_4489_, lean_object* v_b_4490_, lean_object* v_a_4491_){
_start:
{
lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v_cacheKey_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
lean_inc(v_a_4489_);
v___x_4492_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_4489_);
lean_inc(v_b_4490_);
v___x_4493_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_4490_);
v_cacheKey_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_4494_, 0, v___x_4492_);
lean_ctor_set(v_cacheKey_4494_, 1, v___x_4493_);
lean_inc_ref(v_inst_4487_);
v___x_4495_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_4495_, 0, lean_box(0));
lean_closure_set(v___x_4495_, 1, v_inst_4487_);
lean_inc_ref(v_inst_4488_);
v___x_4496_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_4496_, 0, lean_box(0));
lean_closure_set(v___x_4496_, 1, v_inst_4488_);
lean_inc_ref(v_cacheKey_4494_);
lean_inc_ref(v___x_4496_);
lean_inc_ref(v___x_4495_);
v___x_4497_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_4495_, v___x_4496_, v_a_4491_, v_cacheKey_4494_);
if (lean_obj_tag(v___x_4497_) == 1)
{
lean_object* v_val_4498_; lean_object* v___x_4499_; 
lean_dec_ref(v___x_4496_);
lean_dec_ref(v___x_4495_);
lean_dec_ref_known(v_cacheKey_4494_, 2);
lean_dec(v_b_4490_);
lean_dec(v_a_4489_);
lean_dec_ref(v_inst_4488_);
lean_dec_ref(v_inst_4487_);
v_val_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_val_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v___x_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4499_, 0, v_val_4498_);
lean_ctor_set(v___x_4499_, 1, v_a_4491_);
return v___x_4499_;
}
else
{
lean_object* v___x_4500_; lean_object* v_fst_4501_; lean_object* v_snd_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4510_; 
lean_dec(v___x_4497_);
v___x_4500_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_4487_, v_inst_4488_, v_a_4489_, v_b_4490_, v_a_4491_);
v_fst_4501_ = lean_ctor_get(v___x_4500_, 0);
v_snd_4502_ = lean_ctor_get(v___x_4500_, 1);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4504_ = v___x_4500_;
v_isShared_4505_ = v_isSharedCheck_4510_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_snd_4502_);
lean_inc(v_fst_4501_);
lean_dec(v___x_4500_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4510_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4508_; 
lean_inc(v_fst_4501_);
v___x_4506_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_4495_, v___x_4496_, v_snd_4502_, v_cacheKey_4494_, v_fst_4501_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 1, v___x_4506_);
v___x_4508_ = v___x_4504_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_fst_4501_);
lean_ctor_set(v_reuseFailAlloc_4509_, 1, v___x_4506_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
return v___x_4508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized(lean_object* v_00_u03c4_4511_, lean_object* v_inst_4512_, lean_object* v_inst_4513_, lean_object* v_a_4514_, lean_object* v_b_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4512_, v_inst_4513_, v_a_4514_, v_b_4515_, v_a_4516_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go(lean_object* v_00_u03c4_4518_, lean_object* v_inst_4519_, lean_object* v_inst_4520_, lean_object* v_a_4521_, lean_object* v_b_4522_, lean_object* v_a_4523_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_4519_, v_inst_4520_, v_a_4521_, v_b_4522_, v_a_4523_);
return v___x_4524_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4525_ = lean_box(0);
v___x_4526_ = lean_unsigned_to_nat(16u);
v___x_4527_ = lean_mk_array(v___x_4526_, v___x_4525_);
return v___x_4527_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__1(void){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4528_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__0, &l_Lean_Fmt_Doc_beq___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__0);
v___x_4529_ = lean_unsigned_to_nat(0u);
v___x_4530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4529_);
lean_ctor_set(v___x_4530_, 1, v___x_4528_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___redArg(lean_object* v_inst_4531_, lean_object* v_inst_4532_, lean_object* v_a_4533_, lean_object* v_b_4534_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v_fst_4537_; 
v___x_4535_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__1, &l_Lean_Fmt_Doc_beq___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__1);
v___x_4536_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_4531_, v_inst_4532_, v_a_4533_, v_b_4534_, v___x_4535_);
v_fst_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_fst_4537_);
lean_dec_ref(v___x_4536_);
return v_fst_4537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq(lean_object* v_00_u03c4_4538_, lean_object* v_inst_4539_, lean_object* v_inst_4540_, lean_object* v_a_4541_, lean_object* v_b_4542_){
_start:
{
lean_object* v___x_4543_; uint8_t v___x_4544_; 
v___x_4543_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_4539_, v_inst_4540_, v_a_4541_, v_b_4542_);
v___x_4544_ = lean_unbox(v___x_4543_);
lean_dec(v___x_4543_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___boxed(lean_object* v_00_u03c4_4545_, lean_object* v_inst_4546_, lean_object* v_inst_4547_, lean_object* v_a_4548_, lean_object* v_b_4549_){
_start:
{
uint8_t v_res_4550_; lean_object* v_r_4551_; 
v_res_4550_ = l_Lean_Fmt_Doc_beq(v_00_u03c4_4545_, v_inst_4546_, v_inst_4547_, v_a_4548_, v_b_4549_);
v_r_4551_ = lean_box(v_res_4550_);
return v_r_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object* v_inst_4552_, lean_object* v_inst_4553_, lean_object* v_a_4554_, lean_object* v_b_4555_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_4552_, v_inst_4553_, v_a_4554_, v_b_4555_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg(lean_object* v_inst_4557_, lean_object* v_inst_4558_){
_start:
{
lean_object* v___f_4559_; 
v___f_4559_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4559_, 0, v_inst_4557_);
lean_closure_set(v___f_4559_, 1, v_inst_4558_);
return v___f_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable(lean_object* v_00_u03c4_4560_, lean_object* v_inst_4561_, lean_object* v_inst_4562_){
_start:
{
lean_object* v___f_4563_; 
v___f_4563_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_4563_, 0, v_inst_4561_);
lean_closure_set(v___f_4563_, 1, v_inst_4562_);
return v___f_4563_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Core_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Fmt_instInhabitedFullnessState___aux__1 = _init_l_Lean_Fmt_instInhabitedFullnessState___aux__1();
l_Lean_Fmt_instInhabitedFullnessState = _init_l_Lean_Fmt_instInhabitedFullnessState();
l_Lean_Fmt_newlineFailureSet = _init_l_Lean_Fmt_newlineFailureSet();
l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet = _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_emptyTextFailureSet();
l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet = _init_l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_textFailureSet_nonEmptyTextFailureSet();
l_Lean_Fmt_instInhabitedTagId___aux__1 = _init_l_Lean_Fmt_instInhabitedTagId___aux__1();
lean_mark_persistent(l_Lean_Fmt_instInhabitedTagId___aux__1);
l_Lean_Fmt_instInhabitedTagId = _init_l_Lean_Fmt_instInhabitedTagId();
lean_mark_persistent(l_Lean_Fmt_instInhabitedTagId);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Core_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Core_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Core_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Core_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

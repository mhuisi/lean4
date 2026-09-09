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
lean_object* l_Option_merge___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
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
uint8_t lean_bool_to_uint8(uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_newline___override___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_newline___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_newline___override___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_newline___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_newline___override___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_Doc_newline___override___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_newline___override___redArg___closed__1 = (const lean_object*)&l_Lean_Fmt_Doc_newline___override___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_text___override___redArg___lam__0(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_text___override___redArg___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Fmt_Doc_text___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_Doc_text___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_text___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_tagged___override___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_tagged___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_tagged___override___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_tagged___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_tagged___override___redArg___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_final___override___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_final___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_final___override___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_final___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_final___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_initial___override___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_initial___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_initial___override___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_initial___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_initial___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_either___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_either___override___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_either___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_either___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___override___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___override___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___override(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___override___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object*);
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
static const lean_string_object l_Lean_Fmt_Doc_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Fmt_Doc_empty___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_empty___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_Doc_nl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Fmt_Doc_nl___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_nl___closed__0_value;
static lean_once_cell_t l_Lean_Fmt_Doc_nl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_nl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_break___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_break___closed__0;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_hardNl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_hardNl___closed__0;
static lean_once_cell_t l_Lean_Fmt_Doc_hardNl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_hardNl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instAppendDoc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instAppendDoc___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instAppendDoc___closed__0 = (const lean_object*)&l_Lean_Fmt_instAppendDoc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Fmt_Doc_fill___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Fmt_Doc_fill___redArg___closed__0;
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
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Fmt_instBEqPtrKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instBEqPtrKey___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instBEqPtrKey___closed__0 = (const lean_object*)&l_Lean_Fmt_instBEqPtrKey___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_instHashablePtrKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_instHashablePtrKey___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instHashablePtrKey___closed__0 = (const lean_object*)&l_Lean_Fmt_instHashablePtrKey___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId___aux__1(void){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(0u);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_unsigned_to_nat(0u);
return v___x_148_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqTagId___aux__1(lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_eq(v_a_149_, v_b_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqTagId___aux__1___boxed(lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
uint8_t v_res_154_; lean_object* v_r_155_; 
v_res_154_ = l_Lean_Fmt_instBEqTagId___aux__1(v_a_152_, v_b_153_);
lean_dec(v_b_153_);
lean_dec(v_a_152_);
v_r_155_ = lean_box(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableTagId___aux__1(lean_object* v_n_158_){
_start:
{
uint64_t v___x_159_; 
v___x_159_ = lean_uint64_of_nat(v_n_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableTagId___aux__1___boxed(lean_object* v_n_160_){
_start:
{
uint64_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Fmt_instHashableTagId___aux__1(v_n_160_);
lean_dec(v_n_160_);
v_r_162_ = lean_box_uint64(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___aux__1(lean_object* v_x_165_, lean_object* v_y_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = lean_nat_dec_lt(v_x_165_, v_y_166_);
if (v___x_167_ == 0)
{
uint8_t v___x_168_; 
v___x_168_ = lean_nat_dec_eq(v_x_165_, v_y_166_);
if (v___x_168_ == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 2;
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 1;
return v___x_170_;
}
}
else
{
uint8_t v___x_171_; 
v___x_171_ = 0;
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___aux__1___boxed(lean_object* v_x_172_, lean_object* v_y_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Fmt_instOrdTagId___aux__1(v_x_172_, v_y_173_);
lean_dec(v_y_173_);
lean_dec(v_x_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___lam__0(lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_nat_dec_lt(v___y_176_, v___y_177_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; 
v___x_179_ = lean_nat_dec_eq(v___y_176_, v___y_177_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
v___x_180_ = 2;
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = 1;
return v___x_181_;
}
}
else
{
uint8_t v___x_182_; 
v___x_182_ = 0;
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___lam__0___boxed(lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Fmt_instOrdTagId___lam__0(v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec(v___y_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___redArg(lean_object* v_n_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = l_Nat_reprFast(v_n_189_);
v___x_191_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1(lean_object* v_n_192_, lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l_Nat_reprFast(v_n_192_);
v___x_195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___boxed(lean_object* v_n_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Fmt_instReprTagId___aux__1(v_n_196_, v_x_197_);
lean_dec(v_x_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0(lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = l_Nat_reprFast(v___y_199_);
v___x_202_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0___boxed(lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Fmt_instReprTagId___lam__0(v___y_203_, v___y_204_);
lean_dec(v___y_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringTagId___aux__1(lean_object* v_n_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Nat_reprFast(v_n_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1(lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_nat_add(v_a_212_, v_b_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1___boxed(lean_object* v_a_215_, lean_object* v_b_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Fmt_instHAddTagIdNat___aux__1(v_a_215_, v_b_216_);
lean_dec(v_b_216_);
lean_dec(v_a_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx(uint8_t v_x_220_){
_start:
{
switch(v_x_220_)
{
case 0:
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(0u);
return v___x_221_;
}
case 1:
{
lean_object* v___x_222_; 
v___x_222_ = lean_unsigned_to_nat(1u);
return v___x_222_;
}
default: 
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(2u);
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___boxed(lean_object* v_x_224_){
_start:
{
uint8_t v_x_boxed_225_; lean_object* v_res_226_; 
v_x_boxed_225_ = lean_unbox(v_x_224_);
v_res_226_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx(v_x_boxed_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(lean_object* v_k_227_){
_start:
{
lean_inc(v_k_227_);
return v_k_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg___boxed(lean_object* v_k_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(v_k_228_);
lean_dec(v_k_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(lean_object* v_motive_230_, lean_object* v_ctorIdx_231_, uint8_t v_t_232_, lean_object* v_h_233_, lean_object* v_k_234_){
_start:
{
lean_inc(v_k_234_);
return v_k_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___boxed(lean_object* v_motive_235_, lean_object* v_ctorIdx_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_k_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(v_motive_235_, v_ctorIdx_236_, v_t_boxed_240_, v_h_238_, v_k_239_);
lean_dec(v_k_239_);
lean_dec(v_ctorIdx_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(lean_object* v_alwaysEmpty_242_){
_start:
{
lean_inc(v_alwaysEmpty_242_);
return v_alwaysEmpty_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg___boxed(lean_object* v_alwaysEmpty_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(v_alwaysEmpty_243_);
lean_dec(v_alwaysEmpty_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_alwaysEmpty_248_){
_start:
{
lean_inc(v_alwaysEmpty_248_);
return v_alwaysEmpty_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_alwaysEmpty_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_alwaysEmpty_252_);
lean_dec(v_alwaysEmpty_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(lean_object* v_alwaysEmptyIfFlattened_255_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_255_);
return v_alwaysEmptyIfFlattened_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg___boxed(lean_object* v_alwaysEmptyIfFlattened_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(v_alwaysEmptyIfFlattened_256_);
lean_dec(v_alwaysEmptyIfFlattened_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_alwaysEmptyIfFlattened_261_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_261_);
return v_alwaysEmptyIfFlattened_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_alwaysEmptyIfFlattened_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_alwaysEmptyIfFlattened_265_);
lean_dec(v_alwaysEmptyIfFlattened_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(lean_object* v_sometimesNonEmpty_268_){
_start:
{
lean_inc(v_sometimesNonEmpty_268_);
return v_sometimesNonEmpty_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg___boxed(lean_object* v_sometimesNonEmpty_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(v_sometimesNonEmpty_269_);
lean_dec(v_sometimesNonEmpty_269_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(lean_object* v_motive_271_, uint8_t v_t_272_, lean_object* v_h_273_, lean_object* v_sometimesNonEmpty_274_){
_start:
{
lean_inc(v_sometimesNonEmpty_274_);
return v_sometimesNonEmpty_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___boxed(lean_object* v_motive_275_, lean_object* v_t_276_, lean_object* v_h_277_, lean_object* v_sometimesNonEmpty_278_){
_start:
{
uint8_t v_t_boxed_279_; lean_object* v_res_280_; 
v_t_boxed_279_ = lean_unbox(v_t_276_);
v_res_280_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(v_motive_275_, v_t_boxed_279_, v_h_277_, v_sometimesNonEmpty_278_);
lean_dec(v_sometimesNonEmpty_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(uint8_t v_x_281_){
_start:
{
switch(v_x_281_)
{
case 0:
{
lean_object* v___x_282_; 
v___x_282_ = lean_unsigned_to_nat(0u);
return v___x_282_;
}
case 1:
{
lean_object* v___x_283_; 
v___x_283_ = lean_unsigned_to_nat(1u);
return v___x_283_;
}
default: 
{
lean_object* v___x_284_; 
v___x_284_ = lean_unsigned_to_nat(2u);
return v___x_284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0___boxed(lean_object* v_x_285_){
_start:
{
uint8_t v_x_68__boxed_286_; lean_object* v_res_287_; 
v_x_68__boxed_286_ = lean_unbox(v_x_285_);
v_res_287_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_x_68__boxed_286_);
return v_res_287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysEmptiness_max(uint8_t v_e1_288_, uint8_t v_e2_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e2_289_);
v___x_291_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e1_288_);
v___x_292_ = lean_nat_dec_le(v___x_290_, v___x_291_);
lean_dec(v___x_291_);
lean_dec(v___x_290_);
if (v___x_292_ == 0)
{
return v_e2_289_;
}
else
{
return v_e1_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___boxed(lean_object* v_e1_293_, lean_object* v_e2_294_){
_start:
{
uint8_t v_e1_boxed_295_; uint8_t v_e2_boxed_296_; uint8_t v_res_297_; lean_object* v_r_298_; 
v_e1_boxed_295_ = lean_unbox(v_e1_293_);
v_e2_boxed_296_ = lean_unbox(v_e2_294_);
v_res_297_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v_e1_boxed_295_, v_e2_boxed_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx(uint8_t v_x_299_){
_start:
{
if (v_x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(0u);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
v___x_301_ = lean_unsigned_to_nat(1u);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___boxed(lean_object* v_x_302_){
_start:
{
uint8_t v_x_boxed_303_; lean_object* v_res_304_; 
v_x_boxed_303_ = lean_unbox(v_x_302_);
v_res_304_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx(v_x_boxed_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(lean_object* v_k_305_){
_start:
{
lean_inc(v_k_305_);
return v_k_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg___boxed(lean_object* v_k_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(v_k_306_);
lean_dec(v_k_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(lean_object* v_motive_308_, lean_object* v_ctorIdx_309_, uint8_t v_t_310_, lean_object* v_h_311_, lean_object* v_k_312_){
_start:
{
lean_inc(v_k_312_);
return v_k_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___boxed(lean_object* v_motive_313_, lean_object* v_ctorIdx_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_k_317_){
_start:
{
uint8_t v_t_boxed_318_; lean_object* v_res_319_; 
v_t_boxed_318_ = lean_unbox(v_t_315_);
v_res_319_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(v_motive_313_, v_ctorIdx_314_, v_t_boxed_318_, v_h_316_, v_k_317_);
lean_dec(v_k_317_);
lean_dec(v_ctorIdx_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(lean_object* v_alwaysNonEmpty_320_){
_start:
{
lean_inc(v_alwaysNonEmpty_320_);
return v_alwaysNonEmpty_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg___boxed(lean_object* v_alwaysNonEmpty_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(v_alwaysNonEmpty_321_);
lean_dec(v_alwaysNonEmpty_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(lean_object* v_motive_323_, uint8_t v_t_324_, lean_object* v_h_325_, lean_object* v_alwaysNonEmpty_326_){
_start:
{
lean_inc(v_alwaysNonEmpty_326_);
return v_alwaysNonEmpty_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___boxed(lean_object* v_motive_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_alwaysNonEmpty_330_){
_start:
{
uint8_t v_t_boxed_331_; lean_object* v_res_332_; 
v_t_boxed_331_ = lean_unbox(v_t_328_);
v_res_332_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(v_motive_327_, v_t_boxed_331_, v_h_329_, v_alwaysNonEmpty_330_);
lean_dec(v_alwaysNonEmpty_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(lean_object* v_sometimesEmpty_333_){
_start:
{
lean_inc(v_sometimesEmpty_333_);
return v_sometimesEmpty_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg___boxed(lean_object* v_sometimesEmpty_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(v_sometimesEmpty_334_);
lean_dec(v_sometimesEmpty_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(lean_object* v_motive_336_, uint8_t v_t_337_, lean_object* v_h_338_, lean_object* v_sometimesEmpty_339_){
_start:
{
lean_inc(v_sometimesEmpty_339_);
return v_sometimesEmpty_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___boxed(lean_object* v_motive_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_sometimesEmpty_343_){
_start:
{
uint8_t v_t_boxed_344_; lean_object* v_res_345_; 
v_t_boxed_344_ = lean_unbox(v_t_341_);
v_res_345_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(v_motive_340_, v_t_boxed_344_, v_h_342_, v_sometimesEmpty_343_);
lean_dec(v_sometimesEmpty_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(uint8_t v_x_346_){
_start:
{
if (v_x_346_ == 0)
{
lean_object* v___x_347_; 
v___x_347_ = lean_unsigned_to_nat(0u);
return v___x_347_;
}
else
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(1u);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0___boxed(lean_object* v_x_349_){
_start:
{
uint8_t v_x_50__boxed_350_; lean_object* v_res_351_; 
v_x_50__boxed_350_ = lean_unbox(v_x_349_);
v_res_351_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_x_50__boxed_350_);
return v_res_351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(uint8_t v_e1_352_, uint8_t v_e2_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e2_353_);
v___x_355_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e1_352_);
v___x_356_ = lean_nat_dec_le(v___x_354_, v___x_355_);
lean_dec(v___x_355_);
lean_dec(v___x_354_);
if (v___x_356_ == 0)
{
return v_e2_353_;
}
else
{
return v_e1_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___boxed(lean_object* v_e1_357_, lean_object* v_e2_358_){
_start:
{
uint8_t v_e1_boxed_359_; uint8_t v_e2_boxed_360_; uint8_t v_res_361_; lean_object* v_r_362_; 
v_e1_boxed_359_ = lean_unbox(v_e1_357_);
v_e2_boxed_360_ = lean_unbox(v_e2_358_);
v_res_361_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v_e1_boxed_359_, v_e2_boxed_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx(uint8_t v_x_363_){
_start:
{
switch(v_x_363_)
{
case 0:
{
lean_object* v___x_364_; 
v___x_364_ = lean_unsigned_to_nat(0u);
return v___x_364_;
}
case 1:
{
lean_object* v___x_365_; 
v___x_365_ = lean_unsigned_to_nat(1u);
return v___x_365_;
}
case 2:
{
lean_object* v___x_366_; 
v___x_366_ = lean_unsigned_to_nat(2u);
return v___x_366_;
}
case 3:
{
lean_object* v___x_367_; 
v___x_367_ = lean_unsigned_to_nat(3u);
return v___x_367_;
}
default: 
{
lean_object* v___x_368_; 
v___x_368_ = lean_unsigned_to_nat(4u);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___boxed(lean_object* v_x_369_){
_start:
{
uint8_t v_x_boxed_370_; lean_object* v_res_371_; 
v_x_boxed_370_ = lean_unbox(v_x_369_);
v_res_371_ = l_Lean_Fmt_Doc_Atomicness_ctorIdx(v_x_boxed_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(lean_object* v_k_372_){
_start:
{
lean_inc(v_k_372_);
return v_k_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg___boxed(lean_object* v_k_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(v_k_373_);
lean_dec(v_k_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim(lean_object* v_motive_375_, lean_object* v_ctorIdx_376_, uint8_t v_t_377_, lean_object* v_h_378_, lean_object* v_k_379_){
_start:
{
lean_inc(v_k_379_);
return v_k_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___boxed(lean_object* v_motive_380_, lean_object* v_ctorIdx_381_, lean_object* v_t_382_, lean_object* v_h_383_, lean_object* v_k_384_){
_start:
{
uint8_t v_t_boxed_385_; lean_object* v_res_386_; 
v_t_boxed_385_ = lean_unbox(v_t_382_);
v_res_386_ = l_Lean_Fmt_Doc_Atomicness_ctorElim(v_motive_380_, v_ctorIdx_381_, v_t_boxed_385_, v_h_383_, v_k_384_);
lean_dec(v_k_384_);
lean_dec(v_ctorIdx_381_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(lean_object* v_atomic_387_){
_start:
{
lean_inc(v_atomic_387_);
return v_atomic_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg___boxed(lean_object* v_atomic_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(v_atomic_388_);
lean_dec(v_atomic_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim(lean_object* v_motive_390_, uint8_t v_t_391_, lean_object* v_h_392_, lean_object* v_atomic_393_){
_start:
{
lean_inc(v_atomic_393_);
return v_atomic_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___boxed(lean_object* v_motive_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_atomic_397_){
_start:
{
uint8_t v_t_boxed_398_; lean_object* v_res_399_; 
v_t_boxed_398_ = lean_unbox(v_t_395_);
v_res_399_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim(v_motive_394_, v_t_boxed_398_, v_h_396_, v_atomic_397_);
lean_dec(v_atomic_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(lean_object* v_atomicIfFlattened_400_){
_start:
{
lean_inc(v_atomicIfFlattened_400_);
return v_atomicIfFlattened_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg___boxed(lean_object* v_atomicIfFlattened_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(v_atomicIfFlattened_401_);
lean_dec(v_atomicIfFlattened_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(lean_object* v_motive_403_, uint8_t v_t_404_, lean_object* v_h_405_, lean_object* v_atomicIfFlattened_406_){
_start:
{
lean_inc(v_atomicIfFlattened_406_);
return v_atomicIfFlattened_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___boxed(lean_object* v_motive_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_atomicIfFlattened_410_){
_start:
{
uint8_t v_t_boxed_411_; lean_object* v_res_412_; 
v_t_boxed_411_ = lean_unbox(v_t_408_);
v_res_412_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(v_motive_407_, v_t_boxed_411_, v_h_409_, v_atomicIfFlattened_410_);
lean_dec(v_atomicIfFlattened_410_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(lean_object* v_compoundAtomic_413_){
_start:
{
lean_inc(v_compoundAtomic_413_);
return v_compoundAtomic_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg___boxed(lean_object* v_compoundAtomic_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(v_compoundAtomic_414_);
lean_dec(v_compoundAtomic_414_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(lean_object* v_motive_416_, uint8_t v_t_417_, lean_object* v_h_418_, lean_object* v_compoundAtomic_419_){
_start:
{
lean_inc(v_compoundAtomic_419_);
return v_compoundAtomic_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___boxed(lean_object* v_motive_420_, lean_object* v_t_421_, lean_object* v_h_422_, lean_object* v_compoundAtomic_423_){
_start:
{
uint8_t v_t_boxed_424_; lean_object* v_res_425_; 
v_t_boxed_424_ = lean_unbox(v_t_421_);
v_res_425_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(v_motive_420_, v_t_boxed_424_, v_h_422_, v_compoundAtomic_423_);
lean_dec(v_compoundAtomic_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(lean_object* v_compoundAtomicIfFlattened_426_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_426_);
return v_compoundAtomicIfFlattened_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg___boxed(lean_object* v_compoundAtomicIfFlattened_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(v_compoundAtomicIfFlattened_427_);
lean_dec(v_compoundAtomicIfFlattened_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(lean_object* v_motive_429_, uint8_t v_t_430_, lean_object* v_h_431_, lean_object* v_compoundAtomicIfFlattened_432_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_432_);
return v_compoundAtomicIfFlattened_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___boxed(lean_object* v_motive_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_compoundAtomicIfFlattened_436_){
_start:
{
uint8_t v_t_boxed_437_; lean_object* v_res_438_; 
v_t_boxed_437_ = lean_unbox(v_t_434_);
v_res_438_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(v_motive_433_, v_t_boxed_437_, v_h_435_, v_compoundAtomicIfFlattened_436_);
lean_dec(v_compoundAtomicIfFlattened_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(lean_object* v_nonAtomic_439_){
_start:
{
lean_inc(v_nonAtomic_439_);
return v_nonAtomic_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg___boxed(lean_object* v_nonAtomic_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(v_nonAtomic_440_);
lean_dec(v_nonAtomic_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(lean_object* v_motive_442_, uint8_t v_t_443_, lean_object* v_h_444_, lean_object* v_nonAtomic_445_){
_start:
{
lean_inc(v_nonAtomic_445_);
return v_nonAtomic_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___boxed(lean_object* v_motive_446_, lean_object* v_t_447_, lean_object* v_h_448_, lean_object* v_nonAtomic_449_){
_start:
{
uint8_t v_t_boxed_450_; lean_object* v_res_451_; 
v_t_boxed_450_ = lean_unbox(v_t_447_);
v_res_451_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(v_motive_446_, v_t_boxed_450_, v_h_448_, v_nonAtomic_449_);
lean_dec(v_nonAtomic_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0(uint8_t v_x_452_){
_start:
{
switch(v_x_452_)
{
case 0:
{
lean_object* v___x_453_; 
v___x_453_ = lean_unsigned_to_nat(0u);
return v___x_453_;
}
case 1:
{
lean_object* v___x_454_; 
v___x_454_ = lean_unsigned_to_nat(1u);
return v___x_454_;
}
case 2:
{
lean_object* v___x_455_; 
v___x_455_ = lean_unsigned_to_nat(2u);
return v___x_455_;
}
case 3:
{
lean_object* v___x_456_; 
v___x_456_ = lean_unsigned_to_nat(3u);
return v___x_456_;
}
default: 
{
lean_object* v___x_457_; 
v___x_457_ = lean_unsigned_to_nat(4u);
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0___boxed(lean_object* v_x_458_){
_start:
{
uint8_t v_x_104__boxed_459_; lean_object* v_res_460_; 
v_x_104__boxed_459_ = lean_unbox(v_x_458_);
v_res_460_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_x_104__boxed_459_);
return v_res_460_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_Atomicness_max(uint8_t v_e1_461_, uint8_t v_e2_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_463_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e2_462_);
v___x_464_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e1_461_);
v___x_465_ = lean_nat_dec_le(v___x_463_, v___x_464_);
lean_dec(v___x_464_);
lean_dec(v___x_463_);
if (v___x_465_ == 0)
{
return v_e2_462_;
}
else
{
return v_e1_461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___boxed(lean_object* v_e1_466_, lean_object* v_e2_467_){
_start:
{
uint8_t v_e1_boxed_468_; uint8_t v_e2_boxed_469_; uint8_t v_res_470_; lean_object* v_r_471_; 
v_e1_boxed_468_ = lean_unbox(v_e1_466_);
v_e2_boxed_469_ = lean_unbox(v_e2_467_);
v_res_470_ = l_Lean_Fmt_Doc_Atomicness_max(v_e1_boxed_468_, v_e2_boxed_469_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Lean_Fmt_instReprAssertion___lam__0___closed__1));
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0___boxed(lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Fmt_instReprAssertion___lam__0(v_x_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec_ref(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg(lean_object* v_x_483_){
_start:
{
switch(lean_obj_tag(v_x_483_))
{
case 0:
{
lean_object* v___x_484_; 
v___x_484_ = lean_unsigned_to_nat(0u);
return v___x_484_;
}
case 1:
{
lean_object* v___x_485_; 
v___x_485_ = lean_unsigned_to_nat(1u);
return v___x_485_;
}
case 2:
{
lean_object* v___x_486_; 
v___x_486_ = lean_unsigned_to_nat(2u);
return v___x_486_;
}
case 3:
{
lean_object* v___x_487_; 
v___x_487_ = lean_unsigned_to_nat(3u);
return v___x_487_;
}
case 4:
{
lean_object* v___x_488_; 
v___x_488_ = lean_unsigned_to_nat(4u);
return v___x_488_;
}
case 5:
{
lean_object* v___x_489_; 
v___x_489_ = lean_unsigned_to_nat(5u);
return v___x_489_;
}
case 6:
{
lean_object* v___x_490_; 
v___x_490_ = lean_unsigned_to_nat(6u);
return v___x_490_;
}
case 7:
{
lean_object* v___x_491_; 
v___x_491_ = lean_unsigned_to_nat(7u);
return v___x_491_;
}
case 8:
{
lean_object* v___x_492_; 
v___x_492_ = lean_unsigned_to_nat(8u);
return v___x_492_;
}
case 9:
{
lean_object* v___x_493_; 
v___x_493_ = lean_unsigned_to_nat(9u);
return v___x_493_;
}
case 10:
{
lean_object* v___x_494_; 
v___x_494_ = lean_unsigned_to_nat(10u);
return v___x_494_;
}
case 11:
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(11u);
return v___x_495_;
}
case 12:
{
lean_object* v___x_496_; 
v___x_496_ = lean_unsigned_to_nat(12u);
return v___x_496_;
}
case 13:
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(13u);
return v___x_497_;
}
case 14:
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(14u);
return v___x_498_;
}
default: 
{
lean_object* v___x_499_; 
v___x_499_ = lean_unsigned_to_nat(15u);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg___boxed(lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Fmt_Doc_ctorIdx___redArg(v_x_500_);
lean_dec(v_x_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx(lean_object* v_00_u03c4_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Fmt_Doc_ctorIdx___redArg(v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___boxed(lean_object* v_00_u03c4_505_, lean_object* v_x_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Fmt_Doc_ctorIdx(v_00_u03c4_505_, v_x_506_);
lean_dec(v_x_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___redArg(lean_object* v_t_508_, lean_object* v_k_509_){
_start:
{
switch(lean_obj_tag(v_t_508_))
{
case 0:
{
return v_k_509_;
}
case 1:
{
lean_object* v_f_510_; lean_object* v___x_511_; 
v_f_510_ = lean_ctor_get(v_t_508_, 0);
lean_inc_ref(v_f_510_);
lean_dec_ref_known(v_t_508_, 1);
v___x_511_ = lean_apply_1(v_k_509_, v_f_510_);
return v___x_511_;
}
case 2:
{
lean_object* v_s_512_; lean_object* v___x_513_; 
v_s_512_ = lean_ctor_get(v_t_508_, 0);
lean_inc_ref(v_s_512_);
lean_dec_ref_known(v_t_508_, 1);
v___x_513_ = lean_apply_1(v_k_509_, v_s_512_);
return v___x_513_;
}
case 3:
{
lean_object* v_id_514_; lean_object* v_d_515_; lean_object* v___x_516_; 
v_id_514_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_id_514_);
v_d_515_ = lean_ctor_get(v_t_508_, 1);
lean_inc(v_d_515_);
lean_dec_ref_known(v_t_508_, 2);
v___x_516_ = lean_apply_2(v_k_509_, v_id_514_, v_d_515_);
return v___x_516_;
}
case 6:
{
lean_object* v_n_517_; uint8_t v_isCumulative_518_; lean_object* v_d_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_n_517_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_n_517_);
v_isCumulative_518_ = lean_ctor_get_uint8(v_t_508_, sizeof(void*)*2);
v_d_519_ = lean_ctor_get(v_t_508_, 1);
lean_inc(v_d_519_);
lean_dec_ref_known(v_t_508_, 2);
v___x_520_ = lean_box(v_isCumulative_518_);
v___x_521_ = lean_apply_3(v_k_509_, v_n_517_, v___x_520_, v_d_519_);
return v___x_521_;
}
case 8:
{
uint8_t v_onlyNonCumulative_522_; lean_object* v_d_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_onlyNonCumulative_522_ = lean_ctor_get_uint8(v_t_508_, sizeof(void*)*1);
v_d_523_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_d_523_);
lean_dec_ref_known(v_t_508_, 1);
v___x_524_ = lean_box(v_onlyNonCumulative_522_);
v___x_525_ = lean_apply_2(v_k_509_, v___x_524_, v_d_523_);
return v___x_525_;
}
case 12:
{
lean_object* v_p_526_; lean_object* v_d_527_; lean_object* v___x_528_; 
v_p_526_ = lean_ctor_get(v_t_508_, 0);
lean_inc_ref(v_p_526_);
v_d_527_ = lean_ctor_get(v_t_508_, 1);
lean_inc(v_d_527_);
lean_dec_ref_known(v_t_508_, 2);
v___x_528_ = lean_apply_2(v_k_509_, v_p_526_, v_d_527_);
return v___x_528_;
}
case 13:
{
lean_object* v_cost_529_; lean_object* v_d_530_; lean_object* v___x_531_; 
v_cost_529_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_cost_529_);
v_d_530_ = lean_ctor_get(v_t_508_, 1);
lean_inc(v_d_530_);
lean_dec_ref_known(v_t_508_, 2);
v___x_531_ = lean_apply_2(v_k_509_, v_cost_529_, v_d_530_);
return v___x_531_;
}
case 14:
{
lean_object* v_a_532_; lean_object* v_b_533_; lean_object* v___x_534_; 
v_a_532_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_a_532_);
v_b_533_ = lean_ctor_get(v_t_508_, 1);
lean_inc(v_b_533_);
lean_dec_ref_known(v_t_508_, 2);
v___x_534_ = lean_apply_2(v_k_509_, v_a_532_, v_b_533_);
return v___x_534_;
}
case 15:
{
lean_object* v_a_535_; lean_object* v_b_536_; lean_object* v___x_537_; 
v_a_535_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_a_535_);
v_b_536_ = lean_ctor_get(v_t_508_, 1);
lean_inc(v_b_536_);
lean_dec_ref_known(v_t_508_, 2);
v___x_537_ = lean_apply_2(v_k_509_, v_a_535_, v_b_536_);
return v___x_537_;
}
default: 
{
lean_object* v_d_538_; lean_object* v___x_539_; 
v_d_538_ = lean_ctor_get(v_t_508_, 0);
lean_inc(v_d_538_);
lean_dec(v_t_508_);
v___x_539_ = lean_apply_1(v_k_509_, v_d_538_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim(lean_object* v_00_u03c4_540_, lean_object* v_motive_541_, lean_object* v_ctorIdx_542_, lean_object* v_t_543_, lean_object* v_h_544_, lean_object* v_k_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_543_, v_k_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___boxed(lean_object* v_00_u03c4_547_, lean_object* v_motive_548_, lean_object* v_ctorIdx_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_k_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Fmt_Doc_ctorElim(v_00_u03c4_547_, v_motive_548_, v_ctorIdx_549_, v_t_550_, v_h_551_, v_k_552_);
lean_dec(v_ctorIdx_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim___redArg(lean_object* v_t_554_, lean_object* v_failure_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_554_, v_failure_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim(lean_object* v_00_u03c4_557_, lean_object* v_motive_558_, lean_object* v_t_559_, lean_object* v_h_560_, lean_object* v_failure_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_559_, v_failure_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim___redArg(lean_object* v_t_563_, lean_object* v_newline_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_563_, v_newline_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim(lean_object* v_00_u03c4_566_, lean_object* v_motive_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_newline_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_568_, v_newline_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim___redArg(lean_object* v_t_572_, lean_object* v_text_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_572_, v_text_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim(lean_object* v_00_u03c4_575_, lean_object* v_motive_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_text_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_577_, v_text_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim___redArg(lean_object* v_t_581_, lean_object* v_tagged_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_581_, v_tagged_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim(lean_object* v_00_u03c4_584_, lean_object* v_motive_585_, lean_object* v_t_586_, lean_object* v_h_587_, lean_object* v_tagged_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_586_, v_tagged_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim___redArg(lean_object* v_t_590_, lean_object* v_flattened_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_590_, v_flattened_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim(lean_object* v_00_u03c4_593_, lean_object* v_motive_594_, lean_object* v_t_595_, lean_object* v_h_596_, lean_object* v_flattened_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_595_, v_flattened_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim___redArg(lean_object* v_t_599_, lean_object* v_unflattenable_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_599_, v_unflattenable_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim(lean_object* v_00_u03c4_602_, lean_object* v_motive_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_unflattenable_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_604_, v_unflattenable_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim___redArg(lean_object* v_t_608_, lean_object* v_indented_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_608_, v_indented_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim(lean_object* v_00_u03c4_611_, lean_object* v_motive_612_, lean_object* v_t_613_, lean_object* v_h_614_, lean_object* v_indented_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_613_, v_indented_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim___redArg(lean_object* v_t_617_, lean_object* v_aligned_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_617_, v_aligned_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim(lean_object* v_00_u03c4_620_, lean_object* v_motive_621_, lean_object* v_t_622_, lean_object* v_h_623_, lean_object* v_aligned_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_622_, v_aligned_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim___redArg(lean_object* v_t_626_, lean_object* v_unindented_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_626_, v_unindented_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim(lean_object* v_00_u03c4_629_, lean_object* v_motive_630_, lean_object* v_t_631_, lean_object* v_h_632_, lean_object* v_unindented_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_631_, v_unindented_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim___redArg(lean_object* v_t_635_, lean_object* v_final_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_635_, v_final_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final_elim(lean_object* v_00_u03c4_638_, lean_object* v_motive_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_final_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_640_, v_final_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim___redArg(lean_object* v_t_644_, lean_object* v_initial_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_644_, v_initial_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial_elim(lean_object* v_00_u03c4_647_, lean_object* v_motive_648_, lean_object* v_t_649_, lean_object* v_h_650_, lean_object* v_initial_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_649_, v_initial_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim___redArg(lean_object* v_t_653_, lean_object* v_free_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_653_, v_free_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim(lean_object* v_00_u03c4_656_, lean_object* v_motive_657_, lean_object* v_t_658_, lean_object* v_h_659_, lean_object* v_free_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_658_, v_free_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim___redArg(lean_object* v_t_662_, lean_object* v_guarded_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_662_, v_guarded_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim(lean_object* v_00_u03c4_665_, lean_object* v_motive_666_, lean_object* v_t_667_, lean_object* v_h_668_, lean_object* v_guarded_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_667_, v_guarded_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim___redArg(lean_object* v_t_671_, lean_object* v_costing_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_671_, v_costing_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim(lean_object* v_00_u03c4_674_, lean_object* v_motive_675_, lean_object* v_t_676_, lean_object* v_h_677_, lean_object* v_costing_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_676_, v_costing_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim___redArg(lean_object* v_t_680_, lean_object* v_either_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_680_, v_either_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim(lean_object* v_00_u03c4_683_, lean_object* v_motive_684_, lean_object* v_t_685_, lean_object* v_h_686_, lean_object* v_either_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_685_, v_either_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim___redArg(lean_object* v_t_689_, lean_object* v_append_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_689_, v_append_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim(lean_object* v_00_u03c4_692_, lean_object* v_motive_693_, lean_object* v_t_694_, lean_object* v_h_695_, lean_object* v_append_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_694_, v_append_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(lean_object* v_x_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_, lean_object* v_h__3_701_, lean_object* v_h__4_702_, lean_object* v_h__5_703_, lean_object* v_h__6_704_, lean_object* v_h__7_705_, lean_object* v_h__8_706_, lean_object* v_h__9_707_, lean_object* v_h__10_708_, lean_object* v_h__11_709_, lean_object* v_h__12_710_, lean_object* v_h__13_711_, lean_object* v_h__14_712_, lean_object* v_h__15_713_, lean_object* v_h__16_714_){
_start:
{
switch(lean_obj_tag(v_x_698_))
{
case 0:
{
lean_object* v___x_715_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
v___x_715_ = lean_apply_1(v_h__1_699_, lean_box(0));
return v___x_715_;
}
case 1:
{
lean_object* v_f_716_; lean_object* v___x_717_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__1_699_);
v_f_716_ = lean_ctor_get(v_x_698_, 0);
lean_inc_ref(v_f_716_);
lean_dec_ref_known(v_x_698_, 1);
v___x_717_ = lean_apply_2(v_h__2_700_, lean_box(0), v_f_716_);
return v___x_717_;
}
case 2:
{
lean_object* v_s_718_; lean_object* v___x_719_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_s_718_ = lean_ctor_get(v_x_698_, 0);
lean_inc_ref(v_s_718_);
lean_dec_ref_known(v_x_698_, 1);
v___x_719_ = lean_apply_2(v_h__3_701_, lean_box(0), v_s_718_);
return v___x_719_;
}
case 3:
{
lean_object* v_id_720_; lean_object* v_d_721_; lean_object* v___x_722_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_id_720_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_id_720_);
v_d_721_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_d_721_);
lean_dec_ref_known(v_x_698_, 2);
v___x_722_ = lean_apply_3(v_h__5_703_, lean_box(0), v_id_720_, v_d_721_);
return v___x_722_;
}
case 4:
{
lean_object* v_d_723_; lean_object* v___x_724_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_d_723_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_d_723_);
lean_dec_ref_known(v_x_698_, 1);
v___x_724_ = lean_apply_2(v_h__4_702_, lean_box(0), v_d_723_);
return v___x_724_;
}
case 5:
{
lean_object* v_d_725_; lean_object* v___x_726_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_d_725_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_d_725_);
lean_dec_ref_known(v_x_698_, 1);
v___x_726_ = lean_apply_2(v_h__12_710_, lean_box(0), v_d_725_);
return v___x_726_;
}
case 6:
{
lean_object* v_n_727_; uint8_t v_isCumulative_728_; lean_object* v_d_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_n_727_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_n_727_);
v_isCumulative_728_ = lean_ctor_get_uint8(v_x_698_, sizeof(void*)*2);
v_d_729_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_d_729_);
lean_dec_ref_known(v_x_698_, 2);
v___x_730_ = lean_box(v_isCumulative_728_);
v___x_731_ = lean_apply_4(v_h__6_704_, lean_box(0), v_n_727_, v___x_730_, v_d_729_);
return v___x_731_;
}
case 7:
{
lean_object* v_d_732_; lean_object* v___x_733_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_d_732_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_d_732_);
lean_dec_ref_known(v_x_698_, 1);
v___x_733_ = lean_apply_2(v_h__7_705_, lean_box(0), v_d_732_);
return v___x_733_;
}
case 8:
{
uint8_t v_onlyNonCumulative_734_; lean_object* v_d_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_onlyNonCumulative_734_ = lean_ctor_get_uint8(v_x_698_, sizeof(void*)*1);
v_d_735_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_d_735_);
lean_dec_ref_known(v_x_698_, 1);
v___x_736_ = lean_box(v_onlyNonCumulative_734_);
v___x_737_ = lean_apply_3(v_h__8_706_, lean_box(0), v___x_736_, v_d_735_);
return v___x_737_;
}
case 9:
{
lean_object* v_d_738_; lean_object* v___x_739_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_d_738_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_d_738_);
lean_dec_ref_known(v_x_698_, 1);
v___x_739_ = lean_apply_2(v_h__9_707_, lean_box(0), v_d_738_);
return v___x_739_;
}
case 10:
{
lean_object* v_d_740_; lean_object* v___x_741_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_d_740_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_d_740_);
lean_dec_ref_known(v_x_698_, 1);
v___x_741_ = lean_apply_2(v_h__10_708_, lean_box(0), v_d_740_);
return v___x_741_;
}
case 11:
{
lean_object* v_d_742_; lean_object* v___x_743_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_d_742_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_d_742_);
lean_dec_ref_known(v_x_698_, 1);
v___x_743_ = lean_apply_2(v_h__11_709_, lean_box(0), v_d_742_);
return v___x_743_;
}
case 12:
{
lean_object* v_p_744_; lean_object* v_d_745_; lean_object* v___x_746_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_p_744_ = lean_ctor_get(v_x_698_, 0);
lean_inc_ref(v_p_744_);
v_d_745_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_d_745_);
lean_dec_ref_known(v_x_698_, 2);
v___x_746_ = lean_apply_3(v_h__13_711_, lean_box(0), v_p_744_, v_d_745_);
return v___x_746_;
}
case 13:
{
lean_object* v_cost_747_; lean_object* v_d_748_; lean_object* v___x_749_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__15_713_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_cost_747_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_cost_747_);
v_d_748_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_d_748_);
lean_dec_ref_known(v_x_698_, 2);
v___x_749_ = lean_apply_3(v_h__14_712_, lean_box(0), v_cost_747_, v_d_748_);
return v___x_749_;
}
case 14:
{
lean_object* v_a_750_; lean_object* v_b_751_; lean_object* v___x_752_; 
lean_dec(v_h__16_714_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_a_750_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_a_750_);
v_b_751_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_b_751_);
lean_dec_ref_known(v_x_698_, 2);
v___x_752_ = lean_apply_3(v_h__15_713_, lean_box(0), v_a_750_, v_b_751_);
return v___x_752_;
}
default: 
{
lean_object* v_a_753_; lean_object* v_b_754_; lean_object* v___x_755_; 
lean_dec(v_h__15_713_);
lean_dec(v_h__14_712_);
lean_dec(v_h__13_711_);
lean_dec(v_h__12_710_);
lean_dec(v_h__11_709_);
lean_dec(v_h__10_708_);
lean_dec(v_h__9_707_);
lean_dec(v_h__8_706_);
lean_dec(v_h__7_705_);
lean_dec(v_h__6_704_);
lean_dec(v_h__5_703_);
lean_dec(v_h__4_702_);
lean_dec(v_h__3_701_);
lean_dec(v_h__2_700_);
lean_dec(v_h__1_699_);
v_a_753_ = lean_ctor_get(v_x_698_, 0);
lean_inc(v_a_753_);
v_b_754_ = lean_ctor_get(v_x_698_, 1);
lean_inc(v_b_754_);
lean_dec_ref_known(v_x_698_, 2);
v___x_755_ = lean_apply_3(v_h__16_714_, lean_box(0), v_a_753_, v_b_754_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_756_ = _args[0];
lean_object* v_h__1_757_ = _args[1];
lean_object* v_h__2_758_ = _args[2];
lean_object* v_h__3_759_ = _args[3];
lean_object* v_h__4_760_ = _args[4];
lean_object* v_h__5_761_ = _args[5];
lean_object* v_h__6_762_ = _args[6];
lean_object* v_h__7_763_ = _args[7];
lean_object* v_h__8_764_ = _args[8];
lean_object* v_h__9_765_ = _args[9];
lean_object* v_h__10_766_ = _args[10];
lean_object* v_h__11_767_ = _args[11];
lean_object* v_h__12_768_ = _args[12];
lean_object* v_h__13_769_ = _args[13];
lean_object* v_h__14_770_ = _args[14];
lean_object* v_h__15_771_ = _args[15];
lean_object* v_h__16_772_ = _args[16];
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(v_x_756_, v_h__1_757_, v_h__2_758_, v_h__3_759_, v_h__4_760_, v_h__5_761_, v_h__6_762_, v_h__7_763_, v_h__8_764_, v_h__9_765_, v_h__10_766_, v_h__11_767_, v_h__12_768_, v_h__13_769_, v_h__14_770_, v_h__15_771_, v_h__16_772_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(lean_object* v_motive_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_h__1_777_, lean_object* v_h__2_778_, lean_object* v_h__3_779_, lean_object* v_h__4_780_, lean_object* v_h__5_781_, lean_object* v_h__6_782_, lean_object* v_h__7_783_, lean_object* v_h__8_784_, lean_object* v_h__9_785_, lean_object* v_h__10_786_, lean_object* v_h__11_787_, lean_object* v_h__12_788_, lean_object* v_h__13_789_, lean_object* v_h__14_790_, lean_object* v_h__15_791_, lean_object* v_h__16_792_){
_start:
{
switch(lean_obj_tag(v_x_776_))
{
case 0:
{
lean_object* v___x_793_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
v___x_793_ = lean_apply_1(v_h__1_777_, lean_box(0));
return v___x_793_;
}
case 1:
{
lean_object* v_f_794_; lean_object* v___x_795_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__1_777_);
v_f_794_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_f_794_);
lean_dec_ref_known(v_x_776_, 1);
v___x_795_ = lean_apply_2(v_h__2_778_, lean_box(0), v_f_794_);
return v___x_795_;
}
case 2:
{
lean_object* v_s_796_; lean_object* v___x_797_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_s_796_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_s_796_);
lean_dec_ref_known(v_x_776_, 1);
v___x_797_ = lean_apply_2(v_h__3_779_, lean_box(0), v_s_796_);
return v___x_797_;
}
case 3:
{
lean_object* v_id_798_; lean_object* v_d_799_; lean_object* v___x_800_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_id_798_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_id_798_);
v_d_799_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_d_799_);
lean_dec_ref_known(v_x_776_, 2);
v___x_800_ = lean_apply_3(v_h__5_781_, lean_box(0), v_id_798_, v_d_799_);
return v___x_800_;
}
case 4:
{
lean_object* v_d_801_; lean_object* v___x_802_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_d_801_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_d_801_);
lean_dec_ref_known(v_x_776_, 1);
v___x_802_ = lean_apply_2(v_h__4_780_, lean_box(0), v_d_801_);
return v___x_802_;
}
case 5:
{
lean_object* v_d_803_; lean_object* v___x_804_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_d_803_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_d_803_);
lean_dec_ref_known(v_x_776_, 1);
v___x_804_ = lean_apply_2(v_h__12_788_, lean_box(0), v_d_803_);
return v___x_804_;
}
case 6:
{
lean_object* v_n_805_; uint8_t v_isCumulative_806_; lean_object* v_d_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_n_805_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_n_805_);
v_isCumulative_806_ = lean_ctor_get_uint8(v_x_776_, sizeof(void*)*2);
v_d_807_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_d_807_);
lean_dec_ref_known(v_x_776_, 2);
v___x_808_ = lean_box(v_isCumulative_806_);
v___x_809_ = lean_apply_4(v_h__6_782_, lean_box(0), v_n_805_, v___x_808_, v_d_807_);
return v___x_809_;
}
case 7:
{
lean_object* v_d_810_; lean_object* v___x_811_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_d_810_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_d_810_);
lean_dec_ref_known(v_x_776_, 1);
v___x_811_ = lean_apply_2(v_h__7_783_, lean_box(0), v_d_810_);
return v___x_811_;
}
case 8:
{
uint8_t v_onlyNonCumulative_812_; lean_object* v_d_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_onlyNonCumulative_812_ = lean_ctor_get_uint8(v_x_776_, sizeof(void*)*1);
v_d_813_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_d_813_);
lean_dec_ref_known(v_x_776_, 1);
v___x_814_ = lean_box(v_onlyNonCumulative_812_);
v___x_815_ = lean_apply_3(v_h__8_784_, lean_box(0), v___x_814_, v_d_813_);
return v___x_815_;
}
case 9:
{
lean_object* v_d_816_; lean_object* v___x_817_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_d_816_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_d_816_);
lean_dec_ref_known(v_x_776_, 1);
v___x_817_ = lean_apply_2(v_h__9_785_, lean_box(0), v_d_816_);
return v___x_817_;
}
case 10:
{
lean_object* v_d_818_; lean_object* v___x_819_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_d_818_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_d_818_);
lean_dec_ref_known(v_x_776_, 1);
v___x_819_ = lean_apply_2(v_h__10_786_, lean_box(0), v_d_818_);
return v___x_819_;
}
case 11:
{
lean_object* v_d_820_; lean_object* v___x_821_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_d_820_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_d_820_);
lean_dec_ref_known(v_x_776_, 1);
v___x_821_ = lean_apply_2(v_h__11_787_, lean_box(0), v_d_820_);
return v___x_821_;
}
case 12:
{
lean_object* v_p_822_; lean_object* v_d_823_; lean_object* v___x_824_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_p_822_ = lean_ctor_get(v_x_776_, 0);
lean_inc_ref(v_p_822_);
v_d_823_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_d_823_);
lean_dec_ref_known(v_x_776_, 2);
v___x_824_ = lean_apply_3(v_h__13_789_, lean_box(0), v_p_822_, v_d_823_);
return v___x_824_;
}
case 13:
{
lean_object* v_cost_825_; lean_object* v_d_826_; lean_object* v___x_827_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__15_791_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_cost_825_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_cost_825_);
v_d_826_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_d_826_);
lean_dec_ref_known(v_x_776_, 2);
v___x_827_ = lean_apply_3(v_h__14_790_, lean_box(0), v_cost_825_, v_d_826_);
return v___x_827_;
}
case 14:
{
lean_object* v_a_828_; lean_object* v_b_829_; lean_object* v___x_830_; 
lean_dec(v_h__16_792_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_a_828_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_a_828_);
v_b_829_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_b_829_);
lean_dec_ref_known(v_x_776_, 2);
v___x_830_ = lean_apply_3(v_h__15_791_, lean_box(0), v_a_828_, v_b_829_);
return v___x_830_;
}
default: 
{
lean_object* v_a_831_; lean_object* v_b_832_; lean_object* v___x_833_; 
lean_dec(v_h__15_791_);
lean_dec(v_h__14_790_);
lean_dec(v_h__13_789_);
lean_dec(v_h__12_788_);
lean_dec(v_h__11_787_);
lean_dec(v_h__10_786_);
lean_dec(v_h__9_785_);
lean_dec(v_h__8_784_);
lean_dec(v_h__7_783_);
lean_dec(v_h__6_782_);
lean_dec(v_h__5_781_);
lean_dec(v_h__4_780_);
lean_dec(v_h__3_779_);
lean_dec(v_h__2_778_);
lean_dec(v_h__1_777_);
v_a_831_ = lean_ctor_get(v_x_776_, 0);
lean_inc(v_a_831_);
v_b_832_ = lean_ctor_get(v_x_776_, 1);
lean_inc(v_b_832_);
lean_dec_ref_known(v_x_776_, 2);
v___x_833_ = lean_apply_3(v_h__16_792_, lean_box(0), v_a_831_, v_b_832_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___boxed(lean_object** _args){
lean_object* v_motive_834_ = _args[0];
lean_object* v_x_835_ = _args[1];
lean_object* v_x_836_ = _args[2];
lean_object* v_h__1_837_ = _args[3];
lean_object* v_h__2_838_ = _args[4];
lean_object* v_h__3_839_ = _args[5];
lean_object* v_h__4_840_ = _args[6];
lean_object* v_h__5_841_ = _args[7];
lean_object* v_h__6_842_ = _args[8];
lean_object* v_h__7_843_ = _args[9];
lean_object* v_h__8_844_ = _args[10];
lean_object* v_h__9_845_ = _args[11];
lean_object* v_h__10_846_ = _args[12];
lean_object* v_h__11_847_ = _args[13];
lean_object* v_h__12_848_ = _args[14];
lean_object* v_h__13_849_ = _args[15];
lean_object* v_h__14_850_ = _args[16];
lean_object* v_h__15_851_ = _args[17];
lean_object* v_h__16_852_ = _args[18];
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(v_motive_834_, v_x_835_, v_x_836_, v_h__1_837_, v_h__2_838_, v_h__3_839_, v_h__4_840_, v_h__5_841_, v_h__6_842_, v_h__7_843_, v_h__8_844_, v_h__9_845_, v_h__10_846_, v_h__11_847_, v_h__12_848_, v_h__13_849_, v_h__14_850_, v_h__15_851_, v_h__16_852_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(lean_object* v_x_854_, lean_object* v_h__1_855_, lean_object* v_h__2_856_, lean_object* v_h__3_857_, lean_object* v_h__4_858_, lean_object* v_h__5_859_, lean_object* v_h__6_860_, lean_object* v_h__7_861_, lean_object* v_h__8_862_, lean_object* v_h__9_863_, lean_object* v_h__10_864_, lean_object* v_h__11_865_, lean_object* v_h__12_866_, lean_object* v_h__13_867_, lean_object* v_h__14_868_, lean_object* v_h__15_869_, lean_object* v_h__16_870_){
_start:
{
switch(lean_obj_tag(v_x_854_))
{
case 0:
{
lean_object* v___x_871_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
v___x_871_ = lean_apply_1(v_h__1_855_, lean_box(0));
return v___x_871_;
}
case 1:
{
lean_object* v_f_872_; lean_object* v___x_873_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__1_855_);
v_f_872_ = lean_ctor_get(v_x_854_, 0);
lean_inc_ref(v_f_872_);
lean_dec_ref_known(v_x_854_, 1);
v___x_873_ = lean_apply_2(v_h__2_856_, lean_box(0), v_f_872_);
return v___x_873_;
}
case 2:
{
lean_object* v_s_874_; lean_object* v___x_875_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_s_874_ = lean_ctor_get(v_x_854_, 0);
lean_inc_ref(v_s_874_);
lean_dec_ref_known(v_x_854_, 1);
v___x_875_ = lean_apply_2(v_h__3_857_, lean_box(0), v_s_874_);
return v___x_875_;
}
case 3:
{
lean_object* v_id_876_; lean_object* v_d_877_; lean_object* v___x_878_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_id_876_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_id_876_);
v_d_877_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_d_877_);
lean_dec_ref_known(v_x_854_, 2);
v___x_878_ = lean_apply_3(v_h__6_860_, lean_box(0), v_id_876_, v_d_877_);
return v___x_878_;
}
case 4:
{
lean_object* v_d_879_; lean_object* v___x_880_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_d_879_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_d_879_);
lean_dec_ref_known(v_x_854_, 1);
v___x_880_ = lean_apply_2(v_h__4_858_, lean_box(0), v_d_879_);
return v___x_880_;
}
case 5:
{
lean_object* v_d_881_; lean_object* v___x_882_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_d_881_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_d_881_);
lean_dec_ref_known(v_x_854_, 1);
v___x_882_ = lean_apply_2(v_h__5_859_, lean_box(0), v_d_881_);
return v___x_882_;
}
case 6:
{
lean_object* v_n_883_; uint8_t v_isCumulative_884_; lean_object* v_d_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_n_883_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_n_883_);
v_isCumulative_884_ = lean_ctor_get_uint8(v_x_854_, sizeof(void*)*2);
v_d_885_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_d_885_);
lean_dec_ref_known(v_x_854_, 2);
v___x_886_ = lean_box(v_isCumulative_884_);
v___x_887_ = lean_apply_4(v_h__7_861_, lean_box(0), v_n_883_, v___x_886_, v_d_885_);
return v___x_887_;
}
case 7:
{
lean_object* v_d_888_; lean_object* v___x_889_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_d_888_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_d_888_);
lean_dec_ref_known(v_x_854_, 1);
v___x_889_ = lean_apply_2(v_h__8_862_, lean_box(0), v_d_888_);
return v___x_889_;
}
case 8:
{
uint8_t v_onlyNonCumulative_890_; lean_object* v_d_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_onlyNonCumulative_890_ = lean_ctor_get_uint8(v_x_854_, sizeof(void*)*1);
v_d_891_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_d_891_);
lean_dec_ref_known(v_x_854_, 1);
v___x_892_ = lean_box(v_onlyNonCumulative_890_);
v___x_893_ = lean_apply_3(v_h__9_863_, lean_box(0), v___x_892_, v_d_891_);
return v___x_893_;
}
case 9:
{
lean_object* v_d_894_; lean_object* v___x_895_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_d_894_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_d_894_);
lean_dec_ref_known(v_x_854_, 1);
v___x_895_ = lean_apply_2(v_h__10_864_, lean_box(0), v_d_894_);
return v___x_895_;
}
case 10:
{
lean_object* v_d_896_; lean_object* v___x_897_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_d_896_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_d_896_);
lean_dec_ref_known(v_x_854_, 1);
v___x_897_ = lean_apply_2(v_h__11_865_, lean_box(0), v_d_896_);
return v___x_897_;
}
case 11:
{
lean_object* v_d_898_; lean_object* v___x_899_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_d_898_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_d_898_);
lean_dec_ref_known(v_x_854_, 1);
v___x_899_ = lean_apply_2(v_h__12_866_, lean_box(0), v_d_898_);
return v___x_899_;
}
case 12:
{
lean_object* v_p_900_; lean_object* v_d_901_; lean_object* v___x_902_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_p_900_ = lean_ctor_get(v_x_854_, 0);
lean_inc_ref(v_p_900_);
v_d_901_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_d_901_);
lean_dec_ref_known(v_x_854_, 2);
v___x_902_ = lean_apply_3(v_h__13_867_, lean_box(0), v_p_900_, v_d_901_);
return v___x_902_;
}
case 13:
{
lean_object* v_cost_903_; lean_object* v_d_904_; lean_object* v___x_905_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__15_869_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_cost_903_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_cost_903_);
v_d_904_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_d_904_);
lean_dec_ref_known(v_x_854_, 2);
v___x_905_ = lean_apply_3(v_h__14_868_, lean_box(0), v_cost_903_, v_d_904_);
return v___x_905_;
}
case 14:
{
lean_object* v_a_906_; lean_object* v_b_907_; lean_object* v___x_908_; 
lean_dec(v_h__16_870_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_a_906_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_a_906_);
v_b_907_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_b_907_);
lean_dec_ref_known(v_x_854_, 2);
v___x_908_ = lean_apply_3(v_h__15_869_, lean_box(0), v_a_906_, v_b_907_);
return v___x_908_;
}
default: 
{
lean_object* v_a_909_; lean_object* v_b_910_; lean_object* v___x_911_; 
lean_dec(v_h__15_869_);
lean_dec(v_h__14_868_);
lean_dec(v_h__13_867_);
lean_dec(v_h__12_866_);
lean_dec(v_h__11_865_);
lean_dec(v_h__10_864_);
lean_dec(v_h__9_863_);
lean_dec(v_h__8_862_);
lean_dec(v_h__7_861_);
lean_dec(v_h__6_860_);
lean_dec(v_h__5_859_);
lean_dec(v_h__4_858_);
lean_dec(v_h__3_857_);
lean_dec(v_h__2_856_);
lean_dec(v_h__1_855_);
v_a_909_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_a_909_);
v_b_910_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_b_910_);
lean_dec_ref_known(v_x_854_, 2);
v___x_911_ = lean_apply_3(v_h__16_870_, lean_box(0), v_a_909_, v_b_910_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_912_ = _args[0];
lean_object* v_h__1_913_ = _args[1];
lean_object* v_h__2_914_ = _args[2];
lean_object* v_h__3_915_ = _args[3];
lean_object* v_h__4_916_ = _args[4];
lean_object* v_h__5_917_ = _args[5];
lean_object* v_h__6_918_ = _args[6];
lean_object* v_h__7_919_ = _args[7];
lean_object* v_h__8_920_ = _args[8];
lean_object* v_h__9_921_ = _args[9];
lean_object* v_h__10_922_ = _args[10];
lean_object* v_h__11_923_ = _args[11];
lean_object* v_h__12_924_ = _args[12];
lean_object* v_h__13_925_ = _args[13];
lean_object* v_h__14_926_ = _args[14];
lean_object* v_h__15_927_ = _args[15];
lean_object* v_h__16_928_ = _args[16];
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(v_x_912_, v_h__1_913_, v_h__2_914_, v_h__3_915_, v_h__4_916_, v_h__5_917_, v_h__6_918_, v_h__7_919_, v_h__8_920_, v_h__9_921_, v_h__10_922_, v_h__11_923_, v_h__12_924_, v_h__13_925_, v_h__14_926_, v_h__15_927_, v_h__16_928_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(lean_object* v_motive_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_h__1_933_, lean_object* v_h__2_934_, lean_object* v_h__3_935_, lean_object* v_h__4_936_, lean_object* v_h__5_937_, lean_object* v_h__6_938_, lean_object* v_h__7_939_, lean_object* v_h__8_940_, lean_object* v_h__9_941_, lean_object* v_h__10_942_, lean_object* v_h__11_943_, lean_object* v_h__12_944_, lean_object* v_h__13_945_, lean_object* v_h__14_946_, lean_object* v_h__15_947_, lean_object* v_h__16_948_){
_start:
{
switch(lean_obj_tag(v_x_932_))
{
case 0:
{
lean_object* v___x_949_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
v___x_949_ = lean_apply_1(v_h__1_933_, lean_box(0));
return v___x_949_;
}
case 1:
{
lean_object* v_f_950_; lean_object* v___x_951_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__1_933_);
v_f_950_ = lean_ctor_get(v_x_932_, 0);
lean_inc_ref(v_f_950_);
lean_dec_ref_known(v_x_932_, 1);
v___x_951_ = lean_apply_2(v_h__2_934_, lean_box(0), v_f_950_);
return v___x_951_;
}
case 2:
{
lean_object* v_s_952_; lean_object* v___x_953_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_s_952_ = lean_ctor_get(v_x_932_, 0);
lean_inc_ref(v_s_952_);
lean_dec_ref_known(v_x_932_, 1);
v___x_953_ = lean_apply_2(v_h__3_935_, lean_box(0), v_s_952_);
return v___x_953_;
}
case 3:
{
lean_object* v_id_954_; lean_object* v_d_955_; lean_object* v___x_956_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_id_954_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_id_954_);
v_d_955_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_d_955_);
lean_dec_ref_known(v_x_932_, 2);
v___x_956_ = lean_apply_3(v_h__6_938_, lean_box(0), v_id_954_, v_d_955_);
return v___x_956_;
}
case 4:
{
lean_object* v_d_957_; lean_object* v___x_958_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_d_957_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_d_957_);
lean_dec_ref_known(v_x_932_, 1);
v___x_958_ = lean_apply_2(v_h__4_936_, lean_box(0), v_d_957_);
return v___x_958_;
}
case 5:
{
lean_object* v_d_959_; lean_object* v___x_960_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_d_959_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_d_959_);
lean_dec_ref_known(v_x_932_, 1);
v___x_960_ = lean_apply_2(v_h__5_937_, lean_box(0), v_d_959_);
return v___x_960_;
}
case 6:
{
lean_object* v_n_961_; uint8_t v_isCumulative_962_; lean_object* v_d_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_n_961_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_n_961_);
v_isCumulative_962_ = lean_ctor_get_uint8(v_x_932_, sizeof(void*)*2);
v_d_963_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_d_963_);
lean_dec_ref_known(v_x_932_, 2);
v___x_964_ = lean_box(v_isCumulative_962_);
v___x_965_ = lean_apply_4(v_h__7_939_, lean_box(0), v_n_961_, v___x_964_, v_d_963_);
return v___x_965_;
}
case 7:
{
lean_object* v_d_966_; lean_object* v___x_967_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_d_966_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_d_966_);
lean_dec_ref_known(v_x_932_, 1);
v___x_967_ = lean_apply_2(v_h__8_940_, lean_box(0), v_d_966_);
return v___x_967_;
}
case 8:
{
uint8_t v_onlyNonCumulative_968_; lean_object* v_d_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_onlyNonCumulative_968_ = lean_ctor_get_uint8(v_x_932_, sizeof(void*)*1);
v_d_969_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_d_969_);
lean_dec_ref_known(v_x_932_, 1);
v___x_970_ = lean_box(v_onlyNonCumulative_968_);
v___x_971_ = lean_apply_3(v_h__9_941_, lean_box(0), v___x_970_, v_d_969_);
return v___x_971_;
}
case 9:
{
lean_object* v_d_972_; lean_object* v___x_973_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_d_972_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_d_972_);
lean_dec_ref_known(v_x_932_, 1);
v___x_973_ = lean_apply_2(v_h__10_942_, lean_box(0), v_d_972_);
return v___x_973_;
}
case 10:
{
lean_object* v_d_974_; lean_object* v___x_975_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_d_974_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_d_974_);
lean_dec_ref_known(v_x_932_, 1);
v___x_975_ = lean_apply_2(v_h__11_943_, lean_box(0), v_d_974_);
return v___x_975_;
}
case 11:
{
lean_object* v_d_976_; lean_object* v___x_977_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_d_976_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_d_976_);
lean_dec_ref_known(v_x_932_, 1);
v___x_977_ = lean_apply_2(v_h__12_944_, lean_box(0), v_d_976_);
return v___x_977_;
}
case 12:
{
lean_object* v_p_978_; lean_object* v_d_979_; lean_object* v___x_980_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_p_978_ = lean_ctor_get(v_x_932_, 0);
lean_inc_ref(v_p_978_);
v_d_979_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_d_979_);
lean_dec_ref_known(v_x_932_, 2);
v___x_980_ = lean_apply_3(v_h__13_945_, lean_box(0), v_p_978_, v_d_979_);
return v___x_980_;
}
case 13:
{
lean_object* v_cost_981_; lean_object* v_d_982_; lean_object* v___x_983_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__15_947_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_cost_981_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_cost_981_);
v_d_982_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_d_982_);
lean_dec_ref_known(v_x_932_, 2);
v___x_983_ = lean_apply_3(v_h__14_946_, lean_box(0), v_cost_981_, v_d_982_);
return v___x_983_;
}
case 14:
{
lean_object* v_a_984_; lean_object* v_b_985_; lean_object* v___x_986_; 
lean_dec(v_h__16_948_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_a_984_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_a_984_);
v_b_985_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_b_985_);
lean_dec_ref_known(v_x_932_, 2);
v___x_986_ = lean_apply_3(v_h__15_947_, lean_box(0), v_a_984_, v_b_985_);
return v___x_986_;
}
default: 
{
lean_object* v_a_987_; lean_object* v_b_988_; lean_object* v___x_989_; 
lean_dec(v_h__15_947_);
lean_dec(v_h__14_946_);
lean_dec(v_h__13_945_);
lean_dec(v_h__12_944_);
lean_dec(v_h__11_943_);
lean_dec(v_h__10_942_);
lean_dec(v_h__9_941_);
lean_dec(v_h__8_940_);
lean_dec(v_h__7_939_);
lean_dec(v_h__6_938_);
lean_dec(v_h__5_937_);
lean_dec(v_h__4_936_);
lean_dec(v_h__3_935_);
lean_dec(v_h__2_934_);
lean_dec(v_h__1_933_);
v_a_987_ = lean_ctor_get(v_x_932_, 0);
lean_inc(v_a_987_);
v_b_988_ = lean_ctor_get(v_x_932_, 1);
lean_inc(v_b_988_);
lean_dec_ref_known(v_x_932_, 2);
v___x_989_ = lean_apply_3(v_h__16_948_, lean_box(0), v_a_987_, v_b_988_);
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___boxed(lean_object** _args){
lean_object* v_motive_990_ = _args[0];
lean_object* v_x_991_ = _args[1];
lean_object* v_x_992_ = _args[2];
lean_object* v_h__1_993_ = _args[3];
lean_object* v_h__2_994_ = _args[4];
lean_object* v_h__3_995_ = _args[5];
lean_object* v_h__4_996_ = _args[6];
lean_object* v_h__5_997_ = _args[7];
lean_object* v_h__6_998_ = _args[8];
lean_object* v_h__7_999_ = _args[9];
lean_object* v_h__8_1000_ = _args[10];
lean_object* v_h__9_1001_ = _args[11];
lean_object* v_h__10_1002_ = _args[12];
lean_object* v_h__11_1003_ = _args[13];
lean_object* v_h__12_1004_ = _args[14];
lean_object* v_h__13_1005_ = _args[15];
lean_object* v_h__14_1006_ = _args[16];
lean_object* v_h__15_1007_ = _args[17];
lean_object* v_h__16_1008_ = _args[18];
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(v_motive_990_, v_x_991_, v_x_992_, v_h__1_993_, v_h__2_994_, v_h__3_995_, v_h__4_996_, v_h__5_997_, v_h__6_998_, v_h__7_999_, v_h__8_1000_, v_h__9_1001_, v_h__10_1002_, v_h__11_1003_, v_h__12_1004_, v_h__13_1005_, v_h__14_1006_, v_h__15_1007_, v_h__16_1008_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t v_x_1010_, lean_object* v_h__1_1011_, lean_object* v_h__2_1012_, lean_object* v_h__3_1013_){
_start:
{
switch(v_x_1010_)
{
case 0:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v_h__3_1013_);
lean_dec(v_h__2_1012_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_apply_1(v_h__1_1011_, v___x_1014_);
return v___x_1015_;
}
case 1:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v_h__3_1013_);
lean_dec(v_h__1_1011_);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_apply_1(v_h__2_1012_, v___x_1016_);
return v___x_1017_;
}
default: 
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v_h__2_1012_);
lean_dec(v_h__1_1011_);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_apply_1(v_h__3_1013_, v___x_1018_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object* v_x_1020_, lean_object* v_h__1_1021_, lean_object* v_h__2_1022_, lean_object* v_h__3_1023_){
_start:
{
uint8_t v_x_33__boxed_1024_; lean_object* v_res_1025_; 
v_x_33__boxed_1024_ = lean_unbox(v_x_1020_);
v_res_1025_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(v_x_33__boxed_1024_, v_h__1_1021_, v_h__2_1022_, v_h__3_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object* v_motive_1026_, uint8_t v_x_1027_, lean_object* v_h__1_1028_, lean_object* v_h__2_1029_, lean_object* v_h__3_1030_){
_start:
{
switch(v_x_1027_)
{
case 0:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__3_1030_);
lean_dec(v_h__2_1029_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_apply_1(v_h__1_1028_, v___x_1031_);
return v___x_1032_;
}
case 1:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec(v_h__3_1030_);
lean_dec(v_h__1_1028_);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_apply_1(v_h__2_1029_, v___x_1033_);
return v___x_1034_;
}
default: 
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_dec(v_h__2_1029_);
lean_dec(v_h__1_1028_);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_apply_1(v_h__3_1030_, v___x_1035_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object* v_motive_1037_, lean_object* v_x_1038_, lean_object* v_h__1_1039_, lean_object* v_h__2_1040_, lean_object* v_h__3_1041_){
_start:
{
uint8_t v_x_48__boxed_1042_; lean_object* v_res_1043_; 
v_x_48__boxed_1042_ = lean_unbox(v_x_1038_);
v_res_1043_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(v_motive_1037_, v_x_48__boxed_1042_, v_h__1_1039_, v_h__2_1040_, v_h__3_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object* v_x_1044_, lean_object* v_h__1_1045_, lean_object* v_h__2_1046_, lean_object* v_h__3_1047_, lean_object* v_h__4_1048_, lean_object* v_h__5_1049_, lean_object* v_h__6_1050_, lean_object* v_h__7_1051_, lean_object* v_h__8_1052_, lean_object* v_h__9_1053_, lean_object* v_h__10_1054_, lean_object* v_h__11_1055_, lean_object* v_h__12_1056_, lean_object* v_h__13_1057_, lean_object* v_h__14_1058_, lean_object* v_h__15_1059_, lean_object* v_h__16_1060_){
_start:
{
switch(lean_obj_tag(v_x_1044_))
{
case 0:
{
lean_object* v___x_1061_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
v___x_1061_ = lean_apply_1(v_h__1_1045_, lean_box(0));
return v___x_1061_;
}
case 1:
{
lean_object* v_f_1062_; lean_object* v___x_1063_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_f_1062_ = lean_ctor_get(v_x_1044_, 0);
lean_inc_ref(v_f_1062_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1063_ = lean_apply_2(v_h__3_1047_, lean_box(0), v_f_1062_);
return v___x_1063_;
}
case 2:
{
lean_object* v_s_1064_; lean_object* v___x_1065_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__1_1045_);
v_s_1064_ = lean_ctor_get(v_x_1044_, 0);
lean_inc_ref(v_s_1064_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1065_ = lean_apply_2(v_h__2_1046_, lean_box(0), v_s_1064_);
return v___x_1065_;
}
case 3:
{
lean_object* v_id_1066_; lean_object* v_d_1067_; lean_object* v___x_1068_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_id_1066_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_id_1066_);
v_d_1067_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_d_1067_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1068_ = lean_apply_3(v_h__6_1050_, lean_box(0), v_id_1066_, v_d_1067_);
return v___x_1068_;
}
case 4:
{
lean_object* v_d_1069_; lean_object* v___x_1070_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_d_1069_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_d_1069_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1070_ = lean_apply_2(v_h__4_1048_, lean_box(0), v_d_1069_);
return v___x_1070_;
}
case 5:
{
lean_object* v_d_1071_; lean_object* v___x_1072_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_d_1071_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_d_1071_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1072_ = lean_apply_2(v_h__5_1049_, lean_box(0), v_d_1071_);
return v___x_1072_;
}
case 6:
{
lean_object* v_n_1073_; uint8_t v_isCumulative_1074_; lean_object* v_d_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_n_1073_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_n_1073_);
v_isCumulative_1074_ = lean_ctor_get_uint8(v_x_1044_, sizeof(void*)*2);
v_d_1075_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_d_1075_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1076_ = lean_box(v_isCumulative_1074_);
v___x_1077_ = lean_apply_4(v_h__7_1051_, lean_box(0), v_n_1073_, v___x_1076_, v_d_1075_);
return v___x_1077_;
}
case 7:
{
lean_object* v_d_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_d_1078_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_d_1078_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1079_ = lean_apply_2(v_h__8_1052_, lean_box(0), v_d_1078_);
return v___x_1079_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1080_; lean_object* v_d_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_onlyNonCumulative_1080_ = lean_ctor_get_uint8(v_x_1044_, sizeof(void*)*1);
v_d_1081_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_d_1081_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1082_ = lean_box(v_onlyNonCumulative_1080_);
v___x_1083_ = lean_apply_3(v_h__9_1053_, lean_box(0), v___x_1082_, v_d_1081_);
return v___x_1083_;
}
case 9:
{
lean_object* v_d_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_d_1084_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_d_1084_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1085_ = lean_apply_2(v_h__10_1054_, lean_box(0), v_d_1084_);
return v___x_1085_;
}
case 10:
{
lean_object* v_d_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_d_1086_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_d_1086_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1087_ = lean_apply_2(v_h__11_1055_, lean_box(0), v_d_1086_);
return v___x_1087_;
}
case 11:
{
lean_object* v_d_1088_; lean_object* v___x_1089_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_d_1088_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_d_1088_);
lean_dec_ref_known(v_x_1044_, 1);
v___x_1089_ = lean_apply_2(v_h__12_1056_, lean_box(0), v_d_1088_);
return v___x_1089_;
}
case 12:
{
lean_object* v_p_1090_; lean_object* v_d_1091_; lean_object* v___x_1092_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_p_1090_ = lean_ctor_get(v_x_1044_, 0);
lean_inc_ref(v_p_1090_);
v_d_1091_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_d_1091_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1092_ = lean_apply_3(v_h__13_1057_, lean_box(0), v_p_1090_, v_d_1091_);
return v___x_1092_;
}
case 13:
{
lean_object* v_cost_1093_; lean_object* v_d_1094_; lean_object* v___x_1095_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__15_1059_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_cost_1093_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_cost_1093_);
v_d_1094_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_d_1094_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1095_ = lean_apply_3(v_h__14_1058_, lean_box(0), v_cost_1093_, v_d_1094_);
return v___x_1095_;
}
case 14:
{
lean_object* v_a_1096_; lean_object* v_b_1097_; lean_object* v___x_1098_; 
lean_dec(v_h__16_1060_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_a_1096_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1096_);
v_b_1097_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_b_1097_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1098_ = lean_apply_3(v_h__15_1059_, lean_box(0), v_a_1096_, v_b_1097_);
return v___x_1098_;
}
default: 
{
lean_object* v_a_1099_; lean_object* v_b_1100_; lean_object* v___x_1101_; 
lean_dec(v_h__15_1059_);
lean_dec(v_h__14_1058_);
lean_dec(v_h__13_1057_);
lean_dec(v_h__12_1056_);
lean_dec(v_h__11_1055_);
lean_dec(v_h__10_1054_);
lean_dec(v_h__9_1053_);
lean_dec(v_h__8_1052_);
lean_dec(v_h__7_1051_);
lean_dec(v_h__6_1050_);
lean_dec(v_h__5_1049_);
lean_dec(v_h__4_1048_);
lean_dec(v_h__3_1047_);
lean_dec(v_h__2_1046_);
lean_dec(v_h__1_1045_);
v_a_1099_ = lean_ctor_get(v_x_1044_, 0);
lean_inc(v_a_1099_);
v_b_1100_ = lean_ctor_get(v_x_1044_, 1);
lean_inc(v_b_1100_);
lean_dec_ref_known(v_x_1044_, 2);
v___x_1101_ = lean_apply_3(v_h__16_1060_, lean_box(0), v_a_1099_, v_b_1100_);
return v___x_1101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg___boxed(lean_object** _args){
lean_object* v_x_1102_ = _args[0];
lean_object* v_h__1_1103_ = _args[1];
lean_object* v_h__2_1104_ = _args[2];
lean_object* v_h__3_1105_ = _args[3];
lean_object* v_h__4_1106_ = _args[4];
lean_object* v_h__5_1107_ = _args[5];
lean_object* v_h__6_1108_ = _args[6];
lean_object* v_h__7_1109_ = _args[7];
lean_object* v_h__8_1110_ = _args[8];
lean_object* v_h__9_1111_ = _args[9];
lean_object* v_h__10_1112_ = _args[10];
lean_object* v_h__11_1113_ = _args[11];
lean_object* v_h__12_1114_ = _args[12];
lean_object* v_h__13_1115_ = _args[13];
lean_object* v_h__14_1116_ = _args[14];
lean_object* v_h__15_1117_ = _args[15];
lean_object* v_h__16_1118_ = _args[16];
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(v_x_1102_, v_h__1_1103_, v_h__2_1104_, v_h__3_1105_, v_h__4_1106_, v_h__5_1107_, v_h__6_1108_, v_h__7_1109_, v_h__8_1110_, v_h__9_1111_, v_h__10_1112_, v_h__11_1113_, v_h__12_1114_, v_h__13_1115_, v_h__14_1116_, v_h__15_1117_, v_h__16_1118_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object* v_motive_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_h__1_1123_, lean_object* v_h__2_1124_, lean_object* v_h__3_1125_, lean_object* v_h__4_1126_, lean_object* v_h__5_1127_, lean_object* v_h__6_1128_, lean_object* v_h__7_1129_, lean_object* v_h__8_1130_, lean_object* v_h__9_1131_, lean_object* v_h__10_1132_, lean_object* v_h__11_1133_, lean_object* v_h__12_1134_, lean_object* v_h__13_1135_, lean_object* v_h__14_1136_, lean_object* v_h__15_1137_, lean_object* v_h__16_1138_){
_start:
{
switch(lean_obj_tag(v_x_1122_))
{
case 0:
{
lean_object* v___x_1139_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
v___x_1139_ = lean_apply_1(v_h__1_1123_, lean_box(0));
return v___x_1139_;
}
case 1:
{
lean_object* v_f_1140_; lean_object* v___x_1141_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_f_1140_ = lean_ctor_get(v_x_1122_, 0);
lean_inc_ref(v_f_1140_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1141_ = lean_apply_2(v_h__3_1125_, lean_box(0), v_f_1140_);
return v___x_1141_;
}
case 2:
{
lean_object* v_s_1142_; lean_object* v___x_1143_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__1_1123_);
v_s_1142_ = lean_ctor_get(v_x_1122_, 0);
lean_inc_ref(v_s_1142_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1143_ = lean_apply_2(v_h__2_1124_, lean_box(0), v_s_1142_);
return v___x_1143_;
}
case 3:
{
lean_object* v_id_1144_; lean_object* v_d_1145_; lean_object* v___x_1146_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_id_1144_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_id_1144_);
v_d_1145_ = lean_ctor_get(v_x_1122_, 1);
lean_inc(v_d_1145_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1146_ = lean_apply_3(v_h__6_1128_, lean_box(0), v_id_1144_, v_d_1145_);
return v___x_1146_;
}
case 4:
{
lean_object* v_d_1147_; lean_object* v___x_1148_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_d_1147_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_d_1147_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1148_ = lean_apply_2(v_h__4_1126_, lean_box(0), v_d_1147_);
return v___x_1148_;
}
case 5:
{
lean_object* v_d_1149_; lean_object* v___x_1150_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_d_1149_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_d_1149_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1150_ = lean_apply_2(v_h__5_1127_, lean_box(0), v_d_1149_);
return v___x_1150_;
}
case 6:
{
lean_object* v_n_1151_; uint8_t v_isCumulative_1152_; lean_object* v_d_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_n_1151_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_n_1151_);
v_isCumulative_1152_ = lean_ctor_get_uint8(v_x_1122_, sizeof(void*)*2);
v_d_1153_ = lean_ctor_get(v_x_1122_, 1);
lean_inc(v_d_1153_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1154_ = lean_box(v_isCumulative_1152_);
v___x_1155_ = lean_apply_4(v_h__7_1129_, lean_box(0), v_n_1151_, v___x_1154_, v_d_1153_);
return v___x_1155_;
}
case 7:
{
lean_object* v_d_1156_; lean_object* v___x_1157_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_d_1156_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_d_1156_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1157_ = lean_apply_2(v_h__8_1130_, lean_box(0), v_d_1156_);
return v___x_1157_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1158_; lean_object* v_d_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_onlyNonCumulative_1158_ = lean_ctor_get_uint8(v_x_1122_, sizeof(void*)*1);
v_d_1159_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_d_1159_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1160_ = lean_box(v_onlyNonCumulative_1158_);
v___x_1161_ = lean_apply_3(v_h__9_1131_, lean_box(0), v___x_1160_, v_d_1159_);
return v___x_1161_;
}
case 9:
{
lean_object* v_d_1162_; lean_object* v___x_1163_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_d_1162_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_d_1162_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1163_ = lean_apply_2(v_h__10_1132_, lean_box(0), v_d_1162_);
return v___x_1163_;
}
case 10:
{
lean_object* v_d_1164_; lean_object* v___x_1165_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_d_1164_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_d_1164_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1165_ = lean_apply_2(v_h__11_1133_, lean_box(0), v_d_1164_);
return v___x_1165_;
}
case 11:
{
lean_object* v_d_1166_; lean_object* v___x_1167_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_d_1166_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_d_1166_);
lean_dec_ref_known(v_x_1122_, 1);
v___x_1167_ = lean_apply_2(v_h__12_1134_, lean_box(0), v_d_1166_);
return v___x_1167_;
}
case 12:
{
lean_object* v_p_1168_; lean_object* v_d_1169_; lean_object* v___x_1170_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_p_1168_ = lean_ctor_get(v_x_1122_, 0);
lean_inc_ref(v_p_1168_);
v_d_1169_ = lean_ctor_get(v_x_1122_, 1);
lean_inc(v_d_1169_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1170_ = lean_apply_3(v_h__13_1135_, lean_box(0), v_p_1168_, v_d_1169_);
return v___x_1170_;
}
case 13:
{
lean_object* v_cost_1171_; lean_object* v_d_1172_; lean_object* v___x_1173_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__15_1137_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_cost_1171_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_cost_1171_);
v_d_1172_ = lean_ctor_get(v_x_1122_, 1);
lean_inc(v_d_1172_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1173_ = lean_apply_3(v_h__14_1136_, lean_box(0), v_cost_1171_, v_d_1172_);
return v___x_1173_;
}
case 14:
{
lean_object* v_a_1174_; lean_object* v_b_1175_; lean_object* v___x_1176_; 
lean_dec(v_h__16_1138_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_a_1174_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_a_1174_);
v_b_1175_ = lean_ctor_get(v_x_1122_, 1);
lean_inc(v_b_1175_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1176_ = lean_apply_3(v_h__15_1137_, lean_box(0), v_a_1174_, v_b_1175_);
return v___x_1176_;
}
default: 
{
lean_object* v_a_1177_; lean_object* v_b_1178_; lean_object* v___x_1179_; 
lean_dec(v_h__15_1137_);
lean_dec(v_h__14_1136_);
lean_dec(v_h__13_1135_);
lean_dec(v_h__12_1134_);
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_a_1177_ = lean_ctor_get(v_x_1122_, 0);
lean_inc(v_a_1177_);
v_b_1178_ = lean_ctor_get(v_x_1122_, 1);
lean_inc(v_b_1178_);
lean_dec_ref_known(v_x_1122_, 2);
v___x_1179_ = lean_apply_3(v_h__16_1138_, lean_box(0), v_a_1177_, v_b_1178_);
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object** _args){
lean_object* v_motive_1180_ = _args[0];
lean_object* v_x_1181_ = _args[1];
lean_object* v_x_1182_ = _args[2];
lean_object* v_h__1_1183_ = _args[3];
lean_object* v_h__2_1184_ = _args[4];
lean_object* v_h__3_1185_ = _args[5];
lean_object* v_h__4_1186_ = _args[6];
lean_object* v_h__5_1187_ = _args[7];
lean_object* v_h__6_1188_ = _args[8];
lean_object* v_h__7_1189_ = _args[9];
lean_object* v_h__8_1190_ = _args[10];
lean_object* v_h__9_1191_ = _args[11];
lean_object* v_h__10_1192_ = _args[12];
lean_object* v_h__11_1193_ = _args[13];
lean_object* v_h__12_1194_ = _args[14];
lean_object* v_h__13_1195_ = _args[15];
lean_object* v_h__14_1196_ = _args[16];
lean_object* v_h__15_1197_ = _args[17];
lean_object* v_h__16_1198_ = _args[18];
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(v_motive_1180_, v_x_1181_, v_x_1182_, v_h__1_1183_, v_h__2_1184_, v_h__3_1185_, v_h__4_1186_, v_h__5_1187_, v_h__6_1188_, v_h__7_1189_, v_h__8_1190_, v_h__9_1191_, v_h__10_1192_, v_h__11_1193_, v_h__12_1194_, v_h__13_1195_, v_h__14_1196_, v_h__15_1197_, v_h__16_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t v_x_1200_, lean_object* v_h__1_1201_, lean_object* v_h__2_1202_, lean_object* v_h__3_1203_, lean_object* v_h__4_1204_, lean_object* v_h__5_1205_){
_start:
{
switch(v_x_1200_)
{
case 0:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
lean_dec(v_h__5_1205_);
lean_dec(v_h__4_1204_);
lean_dec(v_h__3_1203_);
lean_dec(v_h__2_1202_);
v___x_1206_ = lean_box(0);
v___x_1207_ = lean_apply_1(v_h__1_1201_, v___x_1206_);
return v___x_1207_;
}
case 1:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_h__5_1205_);
lean_dec(v_h__4_1204_);
lean_dec(v_h__3_1203_);
lean_dec(v_h__1_1201_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_apply_1(v_h__2_1202_, v___x_1208_);
return v___x_1209_;
}
case 2:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v_h__5_1205_);
lean_dec(v_h__4_1204_);
lean_dec(v_h__2_1202_);
lean_dec(v_h__1_1201_);
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_apply_1(v_h__3_1203_, v___x_1210_);
return v___x_1211_;
}
case 3:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec(v_h__5_1205_);
lean_dec(v_h__3_1203_);
lean_dec(v_h__2_1202_);
lean_dec(v_h__1_1201_);
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_apply_1(v_h__4_1204_, v___x_1212_);
return v___x_1213_;
}
default: 
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_h__4_1204_);
lean_dec(v_h__3_1203_);
lean_dec(v_h__2_1202_);
lean_dec(v_h__1_1201_);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_apply_1(v_h__5_1205_, v___x_1214_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object* v_x_1216_, lean_object* v_h__1_1217_, lean_object* v_h__2_1218_, lean_object* v_h__3_1219_, lean_object* v_h__4_1220_, lean_object* v_h__5_1221_){
_start:
{
uint8_t v_x_51__boxed_1222_; lean_object* v_res_1223_; 
v_x_51__boxed_1222_ = lean_unbox(v_x_1216_);
v_res_1223_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(v_x_51__boxed_1222_, v_h__1_1217_, v_h__2_1218_, v_h__3_1219_, v_h__4_1220_, v_h__5_1221_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object* v_motive_1224_, uint8_t v_x_1225_, lean_object* v_h__1_1226_, lean_object* v_h__2_1227_, lean_object* v_h__3_1228_, lean_object* v_h__4_1229_, lean_object* v_h__5_1230_){
_start:
{
switch(v_x_1225_)
{
case 0:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
lean_dec(v_h__5_1230_);
lean_dec(v_h__4_1229_);
lean_dec(v_h__3_1228_);
lean_dec(v_h__2_1227_);
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_apply_1(v_h__1_1226_, v___x_1231_);
return v___x_1232_;
}
case 1:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec(v_h__5_1230_);
lean_dec(v_h__4_1229_);
lean_dec(v_h__3_1228_);
lean_dec(v_h__1_1226_);
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_apply_1(v_h__2_1227_, v___x_1233_);
return v___x_1234_;
}
case 2:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_h__5_1230_);
lean_dec(v_h__4_1229_);
lean_dec(v_h__2_1227_);
lean_dec(v_h__1_1226_);
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_apply_1(v_h__3_1228_, v___x_1235_);
return v___x_1236_;
}
case 3:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__5_1230_);
lean_dec(v_h__3_1228_);
lean_dec(v_h__2_1227_);
lean_dec(v_h__1_1226_);
v___x_1237_ = lean_box(0);
v___x_1238_ = lean_apply_1(v_h__4_1229_, v___x_1237_);
return v___x_1238_;
}
default: 
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_dec(v_h__4_1229_);
lean_dec(v_h__3_1228_);
lean_dec(v_h__2_1227_);
lean_dec(v_h__1_1226_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_apply_1(v_h__5_1230_, v___x_1239_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object* v_motive_1241_, lean_object* v_x_1242_, lean_object* v_h__1_1243_, lean_object* v_h__2_1244_, lean_object* v_h__3_1245_, lean_object* v_h__4_1246_, lean_object* v_h__5_1247_){
_start:
{
uint8_t v_x_74__boxed_1248_; lean_object* v_res_1249_; 
v_x_74__boxed_1248_ = lean_unbox(v_x_1242_);
v_res_1249_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(v_motive_1241_, v_x_74__boxed_1248_, v_h__1_1243_, v_h__2_1244_, v_h__3_1245_, v_h__4_1246_, v_h__5_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg(lean_object* v_t_1250_, lean_object* v_failure_1251_, lean_object* v_newline_1252_, lean_object* v_text_1253_, lean_object* v_tagged_1254_, lean_object* v_flattened_1255_, lean_object* v_unflattenable_1256_, lean_object* v_indented_1257_, lean_object* v_aligned_1258_, lean_object* v_unindented_1259_, lean_object* v_final_1260_, lean_object* v_initial_1261_, lean_object* v_free_1262_, lean_object* v_guarded_1263_, lean_object* v_costing_1264_, lean_object* v_either_1265_, lean_object* v_append_1266_){
_start:
{
switch(lean_obj_tag(v_t_1250_))
{
case 0:
{
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
lean_inc(v_failure_1251_);
return v_failure_1251_;
}
case 1:
{
lean_object* v_f_1267_; lean_object* v___x_1268_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
v_f_1267_ = lean_ctor_get(v_t_1250_, 2);
lean_inc_ref(v_f_1267_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1268_ = lean_apply_1(v_newline_1252_, v_f_1267_);
return v___x_1268_;
}
case 2:
{
lean_object* v_s_1269_; lean_object* v___x_1270_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_newline_1252_);
v_s_1269_ = lean_ctor_get(v_t_1250_, 2);
lean_inc_ref(v_s_1269_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1270_ = lean_apply_1(v_text_1253_, v_s_1269_);
return v___x_1270_;
}
case 3:
{
lean_object* v_id_1271_; lean_object* v_d_1272_; lean_object* v___x_1273_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_id_1271_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_id_1271_);
v_d_1272_ = lean_ctor_get(v_t_1250_, 3);
lean_inc(v_d_1272_);
lean_dec_ref_known(v_t_1250_, 4);
v___x_1273_ = lean_apply_2(v_tagged_1254_, v_id_1271_, v_d_1272_);
return v___x_1273_;
}
case 4:
{
lean_object* v_d_1274_; lean_object* v___x_1275_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_d_1274_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_d_1274_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1275_ = lean_apply_1(v_flattened_1255_, v_d_1274_);
return v___x_1275_;
}
case 5:
{
lean_object* v_d_1276_; lean_object* v___x_1277_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_d_1276_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_d_1276_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1277_ = lean_apply_1(v_unflattenable_1256_, v_d_1276_);
return v___x_1277_;
}
case 6:
{
lean_object* v_n_1278_; uint8_t v_isCumulative_1279_; lean_object* v_d_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_n_1278_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_n_1278_);
v_isCumulative_1279_ = lean_ctor_get_uint8(v_t_1250_, sizeof(void*)*4 + 3);
v_d_1280_ = lean_ctor_get(v_t_1250_, 3);
lean_inc(v_d_1280_);
lean_dec_ref_known(v_t_1250_, 4);
v___x_1281_ = lean_box(v_isCumulative_1279_);
v___x_1282_ = lean_apply_3(v_indented_1257_, v_n_1278_, v___x_1281_, v_d_1280_);
return v___x_1282_;
}
case 7:
{
lean_object* v_d_1283_; lean_object* v___x_1284_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_d_1283_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_d_1283_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1284_ = lean_apply_1(v_aligned_1258_, v_d_1283_);
return v___x_1284_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1285_; lean_object* v_d_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_onlyNonCumulative_1285_ = lean_ctor_get_uint8(v_t_1250_, sizeof(void*)*3 + 3);
v_d_1286_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_d_1286_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1287_ = lean_box(v_onlyNonCumulative_1285_);
v___x_1288_ = lean_apply_2(v_unindented_1259_, v___x_1287_, v_d_1286_);
return v___x_1288_;
}
case 9:
{
lean_object* v_d_1289_; lean_object* v___x_1290_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_d_1289_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_d_1289_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1290_ = lean_apply_1(v_final_1260_, v_d_1289_);
return v___x_1290_;
}
case 10:
{
lean_object* v_d_1291_; lean_object* v___x_1292_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_d_1291_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_d_1291_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1292_ = lean_apply_1(v_initial_1261_, v_d_1291_);
return v___x_1292_;
}
case 11:
{
lean_object* v_d_1293_; lean_object* v___x_1294_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_d_1293_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_d_1293_);
lean_dec_ref_known(v_t_1250_, 3);
v___x_1294_ = lean_apply_1(v_free_1262_, v_d_1293_);
return v___x_1294_;
}
case 12:
{
lean_object* v_p_1295_; lean_object* v_d_1296_; lean_object* v___x_1297_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_p_1295_ = lean_ctor_get(v_t_1250_, 2);
lean_inc_ref(v_p_1295_);
v_d_1296_ = lean_ctor_get(v_t_1250_, 3);
lean_inc(v_d_1296_);
lean_dec_ref_known(v_t_1250_, 4);
v___x_1297_ = lean_apply_2(v_guarded_1263_, v_p_1295_, v_d_1296_);
return v___x_1297_;
}
case 13:
{
lean_object* v_cost_1298_; lean_object* v_d_1299_; lean_object* v___x_1300_; 
lean_dec(v_append_1266_);
lean_dec(v_either_1265_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_cost_1298_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_cost_1298_);
v_d_1299_ = lean_ctor_get(v_t_1250_, 3);
lean_inc(v_d_1299_);
lean_dec_ref_known(v_t_1250_, 4);
v___x_1300_ = lean_apply_2(v_costing_1264_, v_cost_1298_, v_d_1299_);
return v___x_1300_;
}
case 14:
{
lean_object* v_a_1301_; lean_object* v_b_1302_; lean_object* v___x_1303_; 
lean_dec(v_append_1266_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_a_1301_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_a_1301_);
v_b_1302_ = lean_ctor_get(v_t_1250_, 3);
lean_inc(v_b_1302_);
lean_dec_ref_known(v_t_1250_, 4);
v___x_1303_ = lean_apply_2(v_either_1265_, v_a_1301_, v_b_1302_);
return v___x_1303_;
}
default: 
{
lean_object* v_a_1304_; lean_object* v_b_1305_; lean_object* v___x_1306_; 
lean_dec(v_either_1265_);
lean_dec(v_costing_1264_);
lean_dec(v_guarded_1263_);
lean_dec(v_free_1262_);
lean_dec(v_initial_1261_);
lean_dec(v_final_1260_);
lean_dec(v_unindented_1259_);
lean_dec(v_aligned_1258_);
lean_dec(v_indented_1257_);
lean_dec(v_unflattenable_1256_);
lean_dec(v_flattened_1255_);
lean_dec(v_tagged_1254_);
lean_dec(v_text_1253_);
lean_dec(v_newline_1252_);
v_a_1304_ = lean_ctor_get(v_t_1250_, 2);
lean_inc(v_a_1304_);
v_b_1305_ = lean_ctor_get(v_t_1250_, 3);
lean_inc(v_b_1305_);
lean_dec_ref_known(v_t_1250_, 4);
v___x_1306_ = lean_apply_2(v_append_1266_, v_a_1304_, v_b_1305_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg___boxed(lean_object** _args){
lean_object* v_t_1307_ = _args[0];
lean_object* v_failure_1308_ = _args[1];
lean_object* v_newline_1309_ = _args[2];
lean_object* v_text_1310_ = _args[3];
lean_object* v_tagged_1311_ = _args[4];
lean_object* v_flattened_1312_ = _args[5];
lean_object* v_unflattenable_1313_ = _args[6];
lean_object* v_indented_1314_ = _args[7];
lean_object* v_aligned_1315_ = _args[8];
lean_object* v_unindented_1316_ = _args[9];
lean_object* v_final_1317_ = _args[10];
lean_object* v_initial_1318_ = _args[11];
lean_object* v_free_1319_ = _args[12];
lean_object* v_guarded_1320_ = _args[13];
lean_object* v_costing_1321_ = _args[14];
lean_object* v_either_1322_ = _args[15];
lean_object* v_append_1323_ = _args[16];
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Fmt_Doc_casesOn___override___redArg(v_t_1307_, v_failure_1308_, v_newline_1309_, v_text_1310_, v_tagged_1311_, v_flattened_1312_, v_unflattenable_1313_, v_indented_1314_, v_aligned_1315_, v_unindented_1316_, v_final_1317_, v_initial_1318_, v_free_1319_, v_guarded_1320_, v_costing_1321_, v_either_1322_, v_append_1323_);
lean_dec(v_failure_1308_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override(lean_object* v_00_u03c4_1325_, lean_object* v_motive_1326_, lean_object* v_t_1327_, lean_object* v_failure_1328_, lean_object* v_newline_1329_, lean_object* v_text_1330_, lean_object* v_tagged_1331_, lean_object* v_flattened_1332_, lean_object* v_unflattenable_1333_, lean_object* v_indented_1334_, lean_object* v_aligned_1335_, lean_object* v_unindented_1336_, lean_object* v_final_1337_, lean_object* v_initial_1338_, lean_object* v_free_1339_, lean_object* v_guarded_1340_, lean_object* v_costing_1341_, lean_object* v_either_1342_, lean_object* v_append_1343_){
_start:
{
switch(lean_obj_tag(v_t_1327_))
{
case 0:
{
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
lean_inc(v_failure_1328_);
return v_failure_1328_;
}
case 1:
{
lean_object* v_f_1344_; lean_object* v___x_1345_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
v_f_1344_ = lean_ctor_get(v_t_1327_, 2);
lean_inc_ref(v_f_1344_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1345_ = lean_apply_1(v_newline_1329_, v_f_1344_);
return v___x_1345_;
}
case 2:
{
lean_object* v_s_1346_; lean_object* v___x_1347_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_newline_1329_);
v_s_1346_ = lean_ctor_get(v_t_1327_, 2);
lean_inc_ref(v_s_1346_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1347_ = lean_apply_1(v_text_1330_, v_s_1346_);
return v___x_1347_;
}
case 3:
{
lean_object* v_id_1348_; lean_object* v_d_1349_; lean_object* v___x_1350_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_id_1348_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_id_1348_);
v_d_1349_ = lean_ctor_get(v_t_1327_, 3);
lean_inc(v_d_1349_);
lean_dec_ref_known(v_t_1327_, 4);
v___x_1350_ = lean_apply_2(v_tagged_1331_, v_id_1348_, v_d_1349_);
return v___x_1350_;
}
case 4:
{
lean_object* v_d_1351_; lean_object* v___x_1352_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_d_1351_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_d_1351_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1352_ = lean_apply_1(v_flattened_1332_, v_d_1351_);
return v___x_1352_;
}
case 5:
{
lean_object* v_d_1353_; lean_object* v___x_1354_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_d_1353_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_d_1353_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1354_ = lean_apply_1(v_unflattenable_1333_, v_d_1353_);
return v___x_1354_;
}
case 6:
{
lean_object* v_n_1355_; uint8_t v_isCumulative_1356_; lean_object* v_d_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_n_1355_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_n_1355_);
v_isCumulative_1356_ = lean_ctor_get_uint8(v_t_1327_, sizeof(void*)*4 + 3);
v_d_1357_ = lean_ctor_get(v_t_1327_, 3);
lean_inc(v_d_1357_);
lean_dec_ref_known(v_t_1327_, 4);
v___x_1358_ = lean_box(v_isCumulative_1356_);
v___x_1359_ = lean_apply_3(v_indented_1334_, v_n_1355_, v___x_1358_, v_d_1357_);
return v___x_1359_;
}
case 7:
{
lean_object* v_d_1360_; lean_object* v___x_1361_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_d_1360_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_d_1360_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1361_ = lean_apply_1(v_aligned_1335_, v_d_1360_);
return v___x_1361_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1362_; lean_object* v_d_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_onlyNonCumulative_1362_ = lean_ctor_get_uint8(v_t_1327_, sizeof(void*)*3 + 3);
v_d_1363_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_d_1363_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1364_ = lean_box(v_onlyNonCumulative_1362_);
v___x_1365_ = lean_apply_2(v_unindented_1336_, v___x_1364_, v_d_1363_);
return v___x_1365_;
}
case 9:
{
lean_object* v_d_1366_; lean_object* v___x_1367_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_d_1366_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_d_1366_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1367_ = lean_apply_1(v_final_1337_, v_d_1366_);
return v___x_1367_;
}
case 10:
{
lean_object* v_d_1368_; lean_object* v___x_1369_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_d_1368_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_d_1368_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1369_ = lean_apply_1(v_initial_1338_, v_d_1368_);
return v___x_1369_;
}
case 11:
{
lean_object* v_d_1370_; lean_object* v___x_1371_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_d_1370_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_d_1370_);
lean_dec_ref_known(v_t_1327_, 3);
v___x_1371_ = lean_apply_1(v_free_1339_, v_d_1370_);
return v___x_1371_;
}
case 12:
{
lean_object* v_p_1372_; lean_object* v_d_1373_; lean_object* v___x_1374_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_p_1372_ = lean_ctor_get(v_t_1327_, 2);
lean_inc_ref(v_p_1372_);
v_d_1373_ = lean_ctor_get(v_t_1327_, 3);
lean_inc(v_d_1373_);
lean_dec_ref_known(v_t_1327_, 4);
v___x_1374_ = lean_apply_2(v_guarded_1340_, v_p_1372_, v_d_1373_);
return v___x_1374_;
}
case 13:
{
lean_object* v_cost_1375_; lean_object* v_d_1376_; lean_object* v___x_1377_; 
lean_dec(v_append_1343_);
lean_dec(v_either_1342_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_cost_1375_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_cost_1375_);
v_d_1376_ = lean_ctor_get(v_t_1327_, 3);
lean_inc(v_d_1376_);
lean_dec_ref_known(v_t_1327_, 4);
v___x_1377_ = lean_apply_2(v_costing_1341_, v_cost_1375_, v_d_1376_);
return v___x_1377_;
}
case 14:
{
lean_object* v_a_1378_; lean_object* v_b_1379_; lean_object* v___x_1380_; 
lean_dec(v_append_1343_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_a_1378_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_a_1378_);
v_b_1379_ = lean_ctor_get(v_t_1327_, 3);
lean_inc(v_b_1379_);
lean_dec_ref_known(v_t_1327_, 4);
v___x_1380_ = lean_apply_2(v_either_1342_, v_a_1378_, v_b_1379_);
return v___x_1380_;
}
default: 
{
lean_object* v_a_1381_; lean_object* v_b_1382_; lean_object* v___x_1383_; 
lean_dec(v_either_1342_);
lean_dec(v_costing_1341_);
lean_dec(v_guarded_1340_);
lean_dec(v_free_1339_);
lean_dec(v_initial_1338_);
lean_dec(v_final_1337_);
lean_dec(v_unindented_1336_);
lean_dec(v_aligned_1335_);
lean_dec(v_indented_1334_);
lean_dec(v_unflattenable_1333_);
lean_dec(v_flattened_1332_);
lean_dec(v_tagged_1331_);
lean_dec(v_text_1330_);
lean_dec(v_newline_1329_);
v_a_1381_ = lean_ctor_get(v_t_1327_, 2);
lean_inc(v_a_1381_);
v_b_1382_ = lean_ctor_get(v_t_1327_, 3);
lean_inc(v_b_1382_);
lean_dec_ref_known(v_t_1327_, 4);
v___x_1383_ = lean_apply_2(v_append_1343_, v_a_1381_, v_b_1382_);
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___boxed(lean_object** _args){
lean_object* v_00_u03c4_1384_ = _args[0];
lean_object* v_motive_1385_ = _args[1];
lean_object* v_t_1386_ = _args[2];
lean_object* v_failure_1387_ = _args[3];
lean_object* v_newline_1388_ = _args[4];
lean_object* v_text_1389_ = _args[5];
lean_object* v_tagged_1390_ = _args[6];
lean_object* v_flattened_1391_ = _args[7];
lean_object* v_unflattenable_1392_ = _args[8];
lean_object* v_indented_1393_ = _args[9];
lean_object* v_aligned_1394_ = _args[10];
lean_object* v_unindented_1395_ = _args[11];
lean_object* v_final_1396_ = _args[12];
lean_object* v_initial_1397_ = _args[13];
lean_object* v_free_1398_ = _args[14];
lean_object* v_guarded_1399_ = _args[15];
lean_object* v_costing_1400_ = _args[16];
lean_object* v_either_1401_ = _args[17];
lean_object* v_append_1402_ = _args[18];
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Fmt_Doc_casesOn___override(v_00_u03c4_1384_, v_motive_1385_, v_t_1386_, v_failure_1387_, v_newline_1388_, v_text_1389_, v_tagged_1390_, v_flattened_1391_, v_unflattenable_1392_, v_indented_1393_, v_aligned_1394_, v_unindented_1395_, v_final_1396_, v_initial_1397_, v_free_1398_, v_guarded_1399_, v_costing_1400_, v_either_1401_, v_append_1402_);
lean_dec(v_failure_1387_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override(lean_object* v_00_u03c4_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_box(0);
return v___x_1405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_newline___override___redArg___lam__0(uint8_t v_state_1406_){
_start:
{
uint8_t v___x_1407_; uint8_t v___x_1408_; uint8_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1407_ = 1;
v___x_1408_ = lean_uint8_land(v_state_1406_, v___x_1407_);
v___x_1409_ = 0;
v___x_1410_ = lean_uint8_dec_eq(v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
uint8_t v___x_1411_; 
v___x_1411_ = 1;
return v___x_1411_;
}
else
{
uint8_t v___x_1412_; uint8_t v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = 8;
v___x_1413_ = lean_uint8_land(v_state_1406_, v___x_1412_);
v___x_1414_ = lean_uint8_dec_eq(v___x_1413_, v___x_1409_);
if (v___x_1414_ == 0)
{
return v___x_1410_;
}
else
{
uint8_t v___x_1415_; 
v___x_1415_ = 0;
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg___lam__0___boxed(lean_object* v_state_1416_){
_start:
{
uint8_t v_state_boxed_1417_; uint8_t v_res_1418_; lean_object* v_r_1419_; 
v_state_boxed_1417_ = lean_unbox(v_state_1416_);
v_res_1418_ = l_Lean_Fmt_Doc_newline___override___redArg___lam__0(v_state_boxed_1417_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object* v_f_1423_){
_start:
{
lean_object* v___f_1424_; lean_object* v___x_1425_; uint8_t v___y_1427_; uint8_t v___y_1428_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; uint8_t v___y_1435_; 
v___f_1424_ = ((lean_object*)(l_Lean_Fmt_Doc_newline___override___redArg___closed__0));
v___x_1425_ = ((lean_object*)(l_Lean_Fmt_Doc_newline___override___redArg___closed__1));
v___x_1431_ = lean_string_utf8_byte_size(v_f_1423_);
v___x_1432_ = lean_unsigned_to_nat(0u);
v___x_1433_ = lean_nat_dec_eq(v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1438_; 
v___x_1438_ = 2;
v___y_1435_ = v___x_1438_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1439_; 
v___x_1439_ = 1;
v___y_1435_ = v___x_1439_;
goto v___jp_1434_;
}
v___jp_1426_:
{
uint8_t v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = 1;
v___x_1430_ = lean_alloc_ctor(1, 3, 3);
lean_ctor_set(v___x_1430_, 0, v___f_1424_);
lean_ctor_set(v___x_1430_, 1, v___x_1425_);
lean_ctor_set(v___x_1430_, 2, v_f_1423_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3, v___y_1427_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 1, v___y_1428_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3 + 2, v___x_1429_);
return v___x_1430_;
}
v___jp_1434_:
{
if (v___x_1433_ == 0)
{
uint8_t v___x_1436_; 
v___x_1436_ = 0;
v___y_1427_ = v___y_1435_;
v___y_1428_ = v___x_1436_;
goto v___jp_1426_;
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = 1;
v___y_1427_ = v___y_1435_;
v___y_1428_ = v___x_1437_;
goto v___jp_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object* v_00_u03c4_1440_, lean_object* v_f_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_Fmt_Doc_newline___override___redArg(v_f_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_text___override___redArg___lam__0(lean_object* v_s_1443_, uint8_t v_before_1444_, uint8_t v_after_1445_){
_start:
{
if (v_before_1444_ == 0)
{
return v_after_1445_;
}
else
{
if (v_after_1445_ == 0)
{
return v_before_1444_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_string_utf8_byte_size(v_s_1443_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_nat_dec_eq(v___x_1446_, v___x_1447_);
if (v___x_1448_ == 0)
{
return v_after_1445_;
}
else
{
uint8_t v___x_1449_; 
v___x_1449_ = 0;
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg___lam__0___boxed(lean_object* v_s_1450_, lean_object* v_before_1451_, lean_object* v_after_1452_){
_start:
{
uint8_t v_before_boxed_1453_; uint8_t v_after_boxed_1454_; uint8_t v_res_1455_; lean_object* v_r_1456_; 
v_before_boxed_1453_ = lean_unbox(v_before_1451_);
v_after_boxed_1454_ = lean_unbox(v_after_1452_);
v_res_1455_ = l_Lean_Fmt_Doc_text___override___redArg___lam__0(v_s_1450_, v_before_boxed_1453_, v_after_boxed_1454_);
lean_dec_ref(v_s_1450_);
v_r_1456_ = lean_box(v_res_1455_);
return v_r_1456_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_text___override___redArg___lam__1(lean_object* v_isFailureFor_1457_, uint8_t v_state_1458_){
_start:
{
uint8_t v___y_1460_; uint8_t v___y_1461_; uint8_t v___y_1476_; uint8_t v___y_1477_; uint8_t v___y_1492_; uint8_t v___x_1499_; uint8_t v___x_1500_; uint8_t v___x_1501_; uint8_t v___x_1502_; 
v___x_1499_ = 2;
v___x_1500_ = lean_uint8_land(v_state_1458_, v___x_1499_);
v___x_1501_ = 0;
v___x_1502_ = lean_uint8_dec_eq(v___x_1500_, v___x_1501_);
if (v___x_1502_ == 0)
{
uint8_t v___x_1503_; 
v___x_1503_ = 1;
v___y_1492_ = v___x_1503_;
goto v___jp_1491_;
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = 0;
v___y_1492_ = v___x_1504_;
goto v___jp_1491_;
}
v___jp_1459_:
{
uint8_t v___x_1462_; uint8_t v___x_1463_; uint8_t v___x_1464_; uint8_t v___x_1465_; 
v___x_1462_ = 4;
v___x_1463_ = lean_uint8_land(v_state_1458_, v___x_1462_);
v___x_1464_ = 0;
v___x_1465_ = lean_uint8_dec_eq(v___x_1463_, v___x_1464_);
if (v___x_1465_ == 0)
{
uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1466_ = 1;
v___x_1467_ = lean_box(v___y_1461_);
v___x_1468_ = lean_box(v___x_1466_);
v___x_1469_ = lean_apply_2(v_isFailureFor_1457_, v___x_1467_, v___x_1468_);
v___x_1470_ = lean_unbox(v___x_1469_);
return v___x_1470_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v___x_1471_ = lean_box(v___y_1461_);
v___x_1472_ = lean_box(v___y_1460_);
v___x_1473_ = lean_apply_2(v_isFailureFor_1457_, v___x_1471_, v___x_1472_);
v___x_1474_ = lean_unbox(v___x_1473_);
return v___x_1474_;
}
}
v___jp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1478_ = lean_box(v___y_1476_);
v___x_1479_ = lean_box(v___y_1477_);
lean_inc_ref(v_isFailureFor_1457_);
v___x_1480_ = lean_apply_2(v_isFailureFor_1457_, v___x_1478_, v___x_1479_);
v___x_1481_ = lean_unbox(v___x_1480_);
if (v___x_1481_ == 0)
{
uint8_t v___x_1482_; uint8_t v___x_1483_; uint8_t v___x_1484_; uint8_t v___x_1485_; 
v___x_1482_ = 8;
v___x_1483_ = lean_uint8_land(v_state_1458_, v___x_1482_);
v___x_1484_ = 0;
v___x_1485_ = lean_uint8_dec_eq(v___x_1483_, v___x_1484_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; uint8_t v___x_1487_; 
v___x_1486_ = 1;
v___x_1487_ = lean_unbox(v___x_1480_);
v___y_1460_ = v___x_1487_;
v___y_1461_ = v___x_1486_;
goto v___jp_1459_;
}
else
{
uint8_t v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = lean_unbox(v___x_1480_);
v___x_1489_ = lean_unbox(v___x_1480_);
v___y_1460_ = v___x_1488_;
v___y_1461_ = v___x_1489_;
goto v___jp_1459_;
}
}
else
{
uint8_t v___x_1490_; 
lean_dec_ref(v_isFailureFor_1457_);
v___x_1490_ = lean_unbox(v___x_1480_);
return v___x_1490_;
}
}
v___jp_1491_:
{
uint8_t v___x_1493_; uint8_t v___x_1494_; uint8_t v___x_1495_; uint8_t v___x_1496_; 
v___x_1493_ = 1;
v___x_1494_ = lean_uint8_land(v_state_1458_, v___x_1493_);
v___x_1495_ = 0;
v___x_1496_ = lean_uint8_dec_eq(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
uint8_t v___x_1497_; 
v___x_1497_ = 1;
v___y_1476_ = v___y_1492_;
v___y_1477_ = v___x_1497_;
goto v___jp_1475_;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = 0;
v___y_1476_ = v___y_1492_;
v___y_1477_ = v___x_1498_;
goto v___jp_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg___lam__1___boxed(lean_object* v_isFailureFor_1505_, lean_object* v_state_1506_){
_start:
{
uint8_t v_state_boxed_1507_; uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_state_boxed_1507_ = lean_unbox(v_state_1506_);
v_res_1508_ = l_Lean_Fmt_Doc_text___override___redArg___lam__1(v_isFailureFor_1505_, v_state_boxed_1507_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object* v_s_1512_){
_start:
{
lean_object* v_isFailureFor_1513_; lean_object* v___f_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___y_1518_; uint8_t v___y_1519_; lean_object* v___x_1522_; uint8_t v___x_1523_; uint8_t v___y_1525_; 
lean_inc_ref(v_s_1512_);
v_isFailureFor_1513_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_text___override___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v_isFailureFor_1513_, 0, v_s_1512_);
v___f_1514_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_text___override___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1514_, 0, v_isFailureFor_1513_);
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
v___x_1522_ = lean_string_utf8_byte_size(v_s_1512_);
v___x_1523_ = lean_nat_dec_eq(v___x_1522_, v___x_1515_);
if (v___x_1523_ == 0)
{
uint8_t v___x_1528_; 
v___x_1528_ = 2;
v___y_1525_ = v___x_1528_;
goto v___jp_1524_;
}
else
{
uint8_t v___x_1529_; 
v___x_1529_ = 0;
v___y_1525_ = v___x_1529_;
goto v___jp_1524_;
}
v___jp_1517_:
{
uint8_t v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = 0;
v___x_1521_ = lean_alloc_ctor(2, 3, 3);
lean_ctor_set(v___x_1521_, 0, v___f_1514_);
lean_ctor_set(v___x_1521_, 1, v___x_1516_);
lean_ctor_set(v___x_1521_, 2, v_s_1512_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*3, v___y_1518_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*3 + 1, v___y_1519_);
lean_ctor_set_uint8(v___x_1521_, sizeof(void*)*3 + 2, v___x_1520_);
return v___x_1521_;
}
v___jp_1524_:
{
if (v___x_1523_ == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = 0;
v___y_1518_ = v___y_1525_;
v___y_1519_ = v___x_1526_;
goto v___jp_1517_;
}
else
{
uint8_t v___x_1527_; 
v___x_1527_ = 1;
v___y_1518_ = v___y_1525_;
v___y_1519_ = v___x_1527_;
goto v___jp_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object* v_00_u03c4_1530_, lean_object* v_s_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_tagged___override___redArg___lam__0(uint8_t v_x_1533_){
_start:
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg___lam__0___boxed(lean_object* v_x_1535_){
_start:
{
uint8_t v_x_1258__boxed_1536_; uint8_t v_res_1537_; lean_object* v_r_1538_; 
v_x_1258__boxed_1536_ = lean_unbox(v_x_1535_);
v_res_1537_ = l_Lean_Fmt_Doc_tagged___override___redArg___lam__0(v_x_1258__boxed_1536_);
v_r_1538_ = lean_box(v_res_1537_);
return v_r_1538_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object* v_x_1539_){
_start:
{
switch(lean_obj_tag(v_x_1539_))
{
case 0:
{
uint8_t v___x_1540_; 
v___x_1540_ = 0;
return v___x_1540_;
}
case 3:
{
uint8_t v_atomicness_1541_; 
v_atomicness_1541_ = lean_ctor_get_uint8(v_x_1539_, sizeof(void*)*4 + 2);
return v_atomicness_1541_;
}
case 6:
{
uint8_t v_atomicness_1542_; 
v_atomicness_1542_ = lean_ctor_get_uint8(v_x_1539_, sizeof(void*)*4 + 2);
return v_atomicness_1542_;
}
case 12:
{
uint8_t v_atomicness_1543_; 
v_atomicness_1543_ = lean_ctor_get_uint8(v_x_1539_, sizeof(void*)*4 + 2);
return v_atomicness_1543_;
}
case 13:
{
uint8_t v_atomicness_1544_; 
v_atomicness_1544_ = lean_ctor_get_uint8(v_x_1539_, sizeof(void*)*4 + 2);
return v_atomicness_1544_;
}
case 14:
{
uint8_t v_atomicness_1545_; 
v_atomicness_1545_ = lean_ctor_get_uint8(v_x_1539_, sizeof(void*)*4 + 2);
return v_atomicness_1545_;
}
case 15:
{
uint8_t v_atomicness_1546_; 
v_atomicness_1546_ = lean_ctor_get_uint8(v_x_1539_, sizeof(void*)*4 + 2);
return v_atomicness_1546_;
}
default: 
{
uint8_t v_atomicness_1547_; 
v_atomicness_1547_ = lean_ctor_get_uint8(v_x_1539_, sizeof(void*)*3 + 2);
return v_atomicness_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object* v_x_1548_){
_start:
{
uint8_t v_res_1549_; lean_object* v_r_1550_; 
v_res_1549_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_1548_);
lean_dec(v_x_1548_);
v_r_1550_ = lean_box(v_res_1549_);
return v_r_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object* v_x_1551_){
_start:
{
if (lean_obj_tag(v_x_1551_) == 0)
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_box(0);
return v___x_1552_;
}
else
{
lean_object* v_maxNewlineCount_x3f_1553_; 
v_maxNewlineCount_x3f_1553_ = lean_ctor_get(v_x_1551_, 1);
lean_inc(v_maxNewlineCount_x3f_1553_);
return v_maxNewlineCount_x3f_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object* v_x_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_1554_);
lean_dec(v_x_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object* v_x_1556_){
_start:
{
switch(lean_obj_tag(v_x_1556_))
{
case 0:
{
uint8_t v___x_1557_; 
v___x_1557_ = 1;
return v___x_1557_;
}
case 3:
{
uint8_t v_alwaysNonEmptiness_1558_; 
v_alwaysNonEmptiness_1558_ = lean_ctor_get_uint8(v_x_1556_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1558_;
}
case 6:
{
uint8_t v_alwaysNonEmptiness_1559_; 
v_alwaysNonEmptiness_1559_ = lean_ctor_get_uint8(v_x_1556_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1559_;
}
case 12:
{
uint8_t v_alwaysNonEmptiness_1560_; 
v_alwaysNonEmptiness_1560_ = lean_ctor_get_uint8(v_x_1556_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1560_;
}
case 13:
{
uint8_t v_alwaysNonEmptiness_1561_; 
v_alwaysNonEmptiness_1561_ = lean_ctor_get_uint8(v_x_1556_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1561_;
}
case 14:
{
uint8_t v_alwaysNonEmptiness_1562_; 
v_alwaysNonEmptiness_1562_ = lean_ctor_get_uint8(v_x_1556_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1562_;
}
case 15:
{
uint8_t v_alwaysNonEmptiness_1563_; 
v_alwaysNonEmptiness_1563_ = lean_ctor_get_uint8(v_x_1556_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1563_;
}
default: 
{
uint8_t v_alwaysNonEmptiness_1564_; 
v_alwaysNonEmptiness_1564_ = lean_ctor_get_uint8(v_x_1556_, sizeof(void*)*3 + 1);
return v_alwaysNonEmptiness_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object* v_x_1565_){
_start:
{
uint8_t v_res_1566_; lean_object* v_r_1567_; 
v_res_1566_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_1565_);
lean_dec(v_x_1565_);
v_r_1567_ = lean_box(v_res_1566_);
return v_r_1567_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object* v_x_1568_){
_start:
{
switch(lean_obj_tag(v_x_1568_))
{
case 0:
{
uint8_t v___x_1569_; 
v___x_1569_ = 2;
return v___x_1569_;
}
case 3:
{
uint8_t v_alwaysEmptiness_1570_; 
v_alwaysEmptiness_1570_ = lean_ctor_get_uint8(v_x_1568_, sizeof(void*)*4);
return v_alwaysEmptiness_1570_;
}
case 6:
{
uint8_t v_alwaysEmptiness_1571_; 
v_alwaysEmptiness_1571_ = lean_ctor_get_uint8(v_x_1568_, sizeof(void*)*4);
return v_alwaysEmptiness_1571_;
}
case 12:
{
uint8_t v_alwaysEmptiness_1572_; 
v_alwaysEmptiness_1572_ = lean_ctor_get_uint8(v_x_1568_, sizeof(void*)*4);
return v_alwaysEmptiness_1572_;
}
case 13:
{
uint8_t v_alwaysEmptiness_1573_; 
v_alwaysEmptiness_1573_ = lean_ctor_get_uint8(v_x_1568_, sizeof(void*)*4);
return v_alwaysEmptiness_1573_;
}
case 14:
{
uint8_t v_alwaysEmptiness_1574_; 
v_alwaysEmptiness_1574_ = lean_ctor_get_uint8(v_x_1568_, sizeof(void*)*4);
return v_alwaysEmptiness_1574_;
}
case 15:
{
uint8_t v_alwaysEmptiness_1575_; 
v_alwaysEmptiness_1575_ = lean_ctor_get_uint8(v_x_1568_, sizeof(void*)*4);
return v_alwaysEmptiness_1575_;
}
default: 
{
uint8_t v_alwaysEmptiness_1576_; 
v_alwaysEmptiness_1576_ = lean_ctor_get_uint8(v_x_1568_, sizeof(void*)*3);
return v_alwaysEmptiness_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object* v_x_1577_){
_start:
{
uint8_t v_res_1578_; lean_object* v_r_1579_; 
v_res_1578_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_1577_);
lean_dec(v_x_1577_);
v_r_1579_ = lean_box(v_res_1578_);
return v_r_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object* v_id_1581_, lean_object* v_d_1582_){
_start:
{
lean_object* v___f_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; uint8_t v___x_1586_; uint8_t v___x_1587_; lean_object* v___x_1588_; 
v___f_1583_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1584_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1582_);
v___x_1585_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1582_);
v___x_1586_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1582_);
v___x_1587_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1582_);
v___x_1588_ = lean_alloc_ctor(3, 4, 3);
lean_ctor_set(v___x_1588_, 0, v___f_1583_);
lean_ctor_set(v___x_1588_, 1, v___x_1584_);
lean_ctor_set(v___x_1588_, 2, v_id_1581_);
lean_ctor_set(v___x_1588_, 3, v_d_1582_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*4, v___x_1585_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*4 + 1, v___x_1586_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*4 + 2, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object* v_00_u03c4_1589_, lean_object* v_id_1590_, lean_object* v_d_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_id_1590_, v_d_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object* v_d_1593_){
_start:
{
lean_object* v___f_1594_; lean_object* v___x_1595_; uint8_t v___y_1597_; uint8_t v___x_1605_; 
v___f_1594_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1595_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
v___x_1605_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1593_);
if (v___x_1605_ == 1)
{
uint8_t v___x_1606_; 
v___x_1606_ = 0;
v___y_1597_ = v___x_1606_;
goto v___jp_1596_;
}
else
{
v___y_1597_ = v___x_1605_;
goto v___jp_1596_;
}
v___jp_1596_:
{
uint8_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1593_);
v___x_1599_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1593_);
switch(v___x_1599_)
{
case 1:
{
uint8_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = 0;
v___x_1601_ = lean_alloc_ctor(4, 3, 3);
lean_ctor_set(v___x_1601_, 0, v___f_1594_);
lean_ctor_set(v___x_1601_, 1, v___x_1595_);
lean_ctor_set(v___x_1601_, 2, v_d_1593_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*3, v___y_1597_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*3 + 1, v___x_1598_);
lean_ctor_set_uint8(v___x_1601_, sizeof(void*)*3 + 2, v___x_1600_);
return v___x_1601_;
}
case 3:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = 2;
v___x_1603_ = lean_alloc_ctor(4, 3, 3);
lean_ctor_set(v___x_1603_, 0, v___f_1594_);
lean_ctor_set(v___x_1603_, 1, v___x_1595_);
lean_ctor_set(v___x_1603_, 2, v_d_1593_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*3, v___y_1597_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*3 + 1, v___x_1598_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*3 + 2, v___x_1602_);
return v___x_1603_;
}
default: 
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(4, 3, 3);
lean_ctor_set(v___x_1604_, 0, v___f_1594_);
lean_ctor_set(v___x_1604_, 1, v___x_1595_);
lean_ctor_set(v___x_1604_, 2, v_d_1593_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*3, v___y_1597_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*3 + 1, v___x_1598_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*3 + 2, v___x_1599_);
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override(lean_object* v_00_u03c4_1607_, lean_object* v_d_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object* v_d_1610_){
_start:
{
lean_object* v___f_1611_; lean_object* v___x_1612_; uint8_t v___y_1614_; uint8_t v___x_1622_; 
v___f_1611_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1612_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1610_);
v___x_1622_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1610_);
if (v___x_1622_ == 1)
{
uint8_t v___x_1623_; 
v___x_1623_ = 2;
v___y_1614_ = v___x_1623_;
goto v___jp_1613_;
}
else
{
v___y_1614_ = v___x_1622_;
goto v___jp_1613_;
}
v___jp_1613_:
{
uint8_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1610_);
v___x_1616_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1610_);
switch(v___x_1616_)
{
case 1:
{
uint8_t v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = 4;
v___x_1618_ = lean_alloc_ctor(5, 3, 3);
lean_ctor_set(v___x_1618_, 0, v___f_1611_);
lean_ctor_set(v___x_1618_, 1, v___x_1612_);
lean_ctor_set(v___x_1618_, 2, v_d_1610_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3, v___y_1614_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 1, v___x_1615_);
lean_ctor_set_uint8(v___x_1618_, sizeof(void*)*3 + 2, v___x_1617_);
return v___x_1618_;
}
case 3:
{
uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = 4;
v___x_1620_ = lean_alloc_ctor(5, 3, 3);
lean_ctor_set(v___x_1620_, 0, v___f_1611_);
lean_ctor_set(v___x_1620_, 1, v___x_1612_);
lean_ctor_set(v___x_1620_, 2, v_d_1610_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3, v___y_1614_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 1, v___x_1615_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 2, v___x_1619_);
return v___x_1620_;
}
default: 
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(5, 3, 3);
lean_ctor_set(v___x_1621_, 0, v___f_1611_);
lean_ctor_set(v___x_1621_, 1, v___x_1612_);
lean_ctor_set(v___x_1621_, 2, v_d_1610_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*3, v___y_1614_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*3 + 1, v___x_1615_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*3 + 2, v___x_1616_);
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override(lean_object* v_00_u03c4_1624_, lean_object* v_d_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v_d_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg(lean_object* v_n_1627_, uint8_t v_isCumulative_1628_, lean_object* v_d_1629_){
_start:
{
lean_object* v___f_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; uint8_t v___x_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; 
v___f_1630_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1631_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1629_);
v___x_1632_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1629_);
v___x_1633_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1629_);
v___x_1634_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1629_);
v___x_1635_ = lean_alloc_ctor(6, 4, 4);
lean_ctor_set(v___x_1635_, 0, v___f_1630_);
lean_ctor_set(v___x_1635_, 1, v___x_1631_);
lean_ctor_set(v___x_1635_, 2, v_n_1627_);
lean_ctor_set(v___x_1635_, 3, v_d_1629_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*4, v___x_1632_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*4 + 1, v___x_1633_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*4 + 2, v___x_1634_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*4 + 3, v_isCumulative_1628_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg___boxed(lean_object* v_n_1636_, lean_object* v_isCumulative_1637_, lean_object* v_d_1638_){
_start:
{
uint8_t v_isCumulative_boxed_1639_; lean_object* v_res_1640_; 
v_isCumulative_boxed_1639_ = lean_unbox(v_isCumulative_1637_);
v_res_1640_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_1636_, v_isCumulative_boxed_1639_, v_d_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override(lean_object* v_00_u03c4_1641_, lean_object* v_n_1642_, uint8_t v_isCumulative_1643_, lean_object* v_d_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_1642_, v_isCumulative_1643_, v_d_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___boxed(lean_object* v_00_u03c4_1646_, lean_object* v_n_1647_, lean_object* v_isCumulative_1648_, lean_object* v_d_1649_){
_start:
{
uint8_t v_isCumulative_boxed_1650_; lean_object* v_res_1651_; 
v_isCumulative_boxed_1650_ = lean_unbox(v_isCumulative_1648_);
v_res_1651_ = l_Lean_Fmt_Doc_indented___override(v_00_u03c4_1646_, v_n_1647_, v_isCumulative_boxed_1650_, v_d_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object* v_d_1652_){
_start:
{
lean_object* v___f_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; uint8_t v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; 
v___f_1653_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1654_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1652_);
v___x_1655_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1652_);
v___x_1656_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1652_);
v___x_1657_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1652_);
v___x_1658_ = lean_alloc_ctor(7, 3, 3);
lean_ctor_set(v___x_1658_, 0, v___f_1653_);
lean_ctor_set(v___x_1658_, 1, v___x_1654_);
lean_ctor_set(v___x_1658_, 2, v_d_1652_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3, v___x_1655_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 1, v___x_1656_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 2, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override(lean_object* v_00_u03c4_1659_, lean_object* v_d_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_d_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t v_onlyNonCumulative_1662_, lean_object* v_d_1663_){
_start:
{
lean_object* v___f_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; lean_object* v___x_1669_; 
v___f_1664_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1665_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1663_);
v___x_1666_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1663_);
v___x_1667_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1663_);
v___x_1668_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1663_);
v___x_1669_ = lean_alloc_ctor(8, 3, 4);
lean_ctor_set(v___x_1669_, 0, v___f_1664_);
lean_ctor_set(v___x_1669_, 1, v___x_1665_);
lean_ctor_set(v___x_1669_, 2, v_d_1663_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3, v___x_1666_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3 + 1, v___x_1667_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3 + 2, v___x_1668_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3 + 3, v_onlyNonCumulative_1662_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg___boxed(lean_object* v_onlyNonCumulative_1670_, lean_object* v_d_1671_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_1672_; lean_object* v_res_1673_; 
v_onlyNonCumulative_boxed_1672_ = lean_unbox(v_onlyNonCumulative_1670_);
v_res_1673_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_boxed_1672_, v_d_1671_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override(lean_object* v_00_u03c4_1674_, uint8_t v_onlyNonCumulative_1675_, lean_object* v_d_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_1675_, v_d_1676_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___boxed(lean_object* v_00_u03c4_1678_, lean_object* v_onlyNonCumulative_1679_, lean_object* v_d_1680_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_1681_; lean_object* v_res_1682_; 
v_onlyNonCumulative_boxed_1681_ = lean_unbox(v_onlyNonCumulative_1679_);
v_res_1682_ = l_Lean_Fmt_Doc_unindented___override(v_00_u03c4_1678_, v_onlyNonCumulative_boxed_1681_, v_d_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_final___override___redArg___lam__0(uint8_t v_x_1683_){
_start:
{
uint8_t v___x_1684_; uint8_t v___x_1685_; uint8_t v___x_1686_; uint8_t v___x_1687_; 
v___x_1684_ = 1;
v___x_1685_ = lean_uint8_land(v_x_1683_, v___x_1684_);
v___x_1686_ = 0;
v___x_1687_ = lean_uint8_dec_eq(v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg___lam__0___boxed(lean_object* v_x_1688_){
_start:
{
uint8_t v_x_1394__boxed_1689_; uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_x_1394__boxed_1689_ = lean_unbox(v_x_1688_);
v_res_1690_ = l_Lean_Fmt_Doc_final___override___redArg___lam__0(v_x_1394__boxed_1689_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override___redArg(lean_object* v_d_1693_){
_start:
{
lean_object* v___f_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; uint8_t v___x_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; 
v___f_1694_ = ((lean_object*)(l_Lean_Fmt_Doc_final___override___redArg___closed__0));
v___x_1695_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1693_);
v___x_1696_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1693_);
v___x_1697_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1693_);
v___x_1698_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1693_);
v___x_1699_ = lean_alloc_ctor(9, 3, 3);
lean_ctor_set(v___x_1699_, 0, v___f_1694_);
lean_ctor_set(v___x_1699_, 1, v___x_1695_);
lean_ctor_set(v___x_1699_, 2, v_d_1693_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*3, v___x_1696_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*3 + 1, v___x_1697_);
lean_ctor_set_uint8(v___x_1699_, sizeof(void*)*3 + 2, v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_final___override(lean_object* v_00_u03c4_1700_, lean_object* v_d_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_Fmt_Doc_final___override___redArg(v_d_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_initial___override___redArg___lam__0(uint8_t v_x_1703_){
_start:
{
uint8_t v___x_1704_; uint8_t v___x_1705_; uint8_t v___x_1706_; uint8_t v___x_1707_; 
v___x_1704_ = 8;
v___x_1705_ = lean_uint8_land(v_x_1703_, v___x_1704_);
v___x_1706_ = 0;
v___x_1707_ = lean_uint8_dec_eq(v___x_1705_, v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg___lam__0___boxed(lean_object* v_x_1708_){
_start:
{
uint8_t v_x_1422__boxed_1709_; uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_x_1422__boxed_1709_ = lean_unbox(v_x_1708_);
v_res_1710_ = l_Lean_Fmt_Doc_initial___override___redArg___lam__0(v_x_1422__boxed_1709_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override___redArg(lean_object* v_d_1713_){
_start:
{
lean_object* v___f_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; uint8_t v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; 
v___f_1714_ = ((lean_object*)(l_Lean_Fmt_Doc_initial___override___redArg___closed__0));
v___x_1715_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1713_);
v___x_1716_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1713_);
v___x_1717_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1713_);
v___x_1718_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1713_);
v___x_1719_ = lean_alloc_ctor(10, 3, 3);
lean_ctor_set(v___x_1719_, 0, v___f_1714_);
lean_ctor_set(v___x_1719_, 1, v___x_1715_);
lean_ctor_set(v___x_1719_, 2, v_d_1713_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*3, v___x_1716_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*3 + 1, v___x_1717_);
lean_ctor_set_uint8(v___x_1719_, sizeof(void*)*3 + 2, v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_initial___override(lean_object* v_00_u03c4_1720_, lean_object* v_d_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Fmt_Doc_initial___override___redArg(v_d_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object* v_d_1723_){
_start:
{
lean_object* v___f_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; uint8_t v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
v___f_1724_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1725_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1723_);
v___x_1726_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1723_);
v___x_1727_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1723_);
v___x_1728_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1723_);
v___x_1729_ = lean_alloc_ctor(11, 3, 3);
lean_ctor_set(v___x_1729_, 0, v___f_1724_);
lean_ctor_set(v___x_1729_, 1, v___x_1725_);
lean_ctor_set(v___x_1729_, 2, v_d_1723_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3, v___x_1726_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 1, v___x_1727_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 2, v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object* v_00_u03c4_1730_, lean_object* v_d_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Fmt_Doc_free___override___redArg(v_d_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object* v_p_1733_, lean_object* v_d_1734_){
_start:
{
lean_object* v___f_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; uint8_t v___x_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; 
v___f_1735_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1736_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1734_);
v___x_1737_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1734_);
v___x_1738_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1734_);
v___x_1739_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1734_);
v___x_1740_ = lean_alloc_ctor(12, 4, 3);
lean_ctor_set(v___x_1740_, 0, v___f_1735_);
lean_ctor_set(v___x_1740_, 1, v___x_1736_);
lean_ctor_set(v___x_1740_, 2, v_p_1733_);
lean_ctor_set(v___x_1740_, 3, v_d_1734_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*4, v___x_1737_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*4 + 1, v___x_1738_);
lean_ctor_set_uint8(v___x_1740_, sizeof(void*)*4 + 2, v___x_1739_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object* v_00_u03c4_1741_, lean_object* v_p_1742_, lean_object* v_d_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_1742_, v_d_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object* v_cost_1745_, lean_object* v_d_1746_){
_start:
{
lean_object* v___f_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; uint8_t v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
v___f_1747_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1748_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1746_);
v___x_1749_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1746_);
v___x_1750_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1746_);
v___x_1751_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1746_);
v___x_1752_ = lean_alloc_ctor(13, 4, 3);
lean_ctor_set(v___x_1752_, 0, v___f_1747_);
lean_ctor_set(v___x_1752_, 1, v___x_1748_);
lean_ctor_set(v___x_1752_, 2, v_cost_1745_);
lean_ctor_set(v___x_1752_, 3, v_d_1746_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*4, v___x_1749_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*4 + 1, v___x_1750_);
lean_ctor_set_uint8(v___x_1752_, sizeof(void*)*4 + 2, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object* v_00_u03c4_1753_, lean_object* v_cost_1754_, lean_object* v_d_1755_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_Fmt_Doc_costing___override___redArg(v_cost_1754_, v_d_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__1(lean_object* v_x1_1757_, lean_object* v_x2_1758_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_nat_dec_le(v_x1_1757_, v_x2_1758_);
if (v___x_1759_ == 0)
{
lean_inc(v_x1_1757_);
return v_x1_1757_;
}
else
{
lean_inc(v_x2_1758_);
return v_x2_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__1___boxed(lean_object* v_x1_1760_, lean_object* v_x2_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Fmt_Doc_either___override___redArg___lam__1(v_x1_1760_, v_x2_1761_);
lean_dec(v_x2_1761_);
lean_dec(v_x1_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object* v_a_1764_, lean_object* v_b_1765_){
_start:
{
lean_object* v___f_1766_; lean_object* v___f_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; uint8_t v___x_1772_; uint8_t v___x_1773_; uint8_t v___x_1774_; uint8_t v___x_1775_; uint8_t v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; 
v___f_1766_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___f_1767_ = ((lean_object*)(l_Lean_Fmt_Doc_either___override___redArg___closed__0));
v___x_1768_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_1764_);
v___x_1769_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_1765_);
v___x_1770_ = l_Option_merge___redArg(v___f_1767_, v___x_1768_, v___x_1769_);
v___x_1771_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_1764_);
v___x_1772_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_1765_);
v___x_1773_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_1771_, v___x_1772_);
v___x_1774_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_1764_);
v___x_1775_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_1765_);
v___x_1776_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_1774_, v___x_1775_);
v___x_1777_ = 4;
v___x_1778_ = lean_alloc_ctor(14, 4, 3);
lean_ctor_set(v___x_1778_, 0, v___f_1766_);
lean_ctor_set(v___x_1778_, 1, v___x_1770_);
lean_ctor_set(v___x_1778_, 2, v_a_1764_);
lean_ctor_set(v___x_1778_, 3, v_b_1765_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*4, v___x_1773_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*4 + 1, v___x_1776_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*4 + 2, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object* v_00_u03c4_1779_, lean_object* v_a_1780_, lean_object* v_b_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Fmt_Doc_either___override___redArg(v_a_1780_, v_b_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object* v_a_1783_, lean_object* v_b_1784_){
_start:
{
lean_object* v___f_1785_; lean_object* v___f_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; uint8_t v___x_1791_; uint8_t v___x_1792_; uint8_t v___x_1793_; uint8_t v___x_1794_; uint8_t v___x_1795_; 
v___f_1785_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___f_1786_ = ((lean_object*)(l_Lean_Fmt_instHAddTagIdNat___closed__0));
v___x_1787_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_1783_);
v___x_1788_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_1784_);
v___x_1789_ = l_Option_merge___redArg(v___f_1786_, v___x_1787_, v___x_1788_);
v___x_1790_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_1783_);
v___x_1791_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_1784_);
v___x_1792_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_1790_, v___x_1791_);
v___x_1793_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_1783_);
v___x_1794_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_1784_);
v___x_1795_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_1793_, v___x_1794_);
if (v___x_1790_ == 0)
{
uint8_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_1784_);
v___x_1797_ = lean_alloc_ctor(15, 4, 3);
lean_ctor_set(v___x_1797_, 0, v___f_1785_);
lean_ctor_set(v___x_1797_, 1, v___x_1789_);
lean_ctor_set(v___x_1797_, 2, v_a_1783_);
lean_ctor_set(v___x_1797_, 3, v_b_1784_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*4, v___x_1792_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*4 + 1, v___x_1795_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*4 + 2, v___x_1796_);
return v___x_1797_;
}
else
{
if (v___x_1791_ == 0)
{
uint8_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_1783_);
v___x_1799_ = lean_alloc_ctor(15, 4, 3);
lean_ctor_set(v___x_1799_, 0, v___f_1785_);
lean_ctor_set(v___x_1799_, 1, v___x_1789_);
lean_ctor_set(v___x_1799_, 2, v_a_1783_);
lean_ctor_set(v___x_1799_, 3, v_b_1784_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*4, v___x_1792_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*4 + 1, v___x_1795_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*4 + 2, v___x_1798_);
return v___x_1799_;
}
else
{
uint8_t v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; uint8_t v___x_1803_; uint8_t v___x_1804_; lean_object* v___x_1805_; 
v___x_1800_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_1783_);
v___x_1801_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_1784_);
v___x_1802_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_1800_, v___x_1801_);
v___x_1803_ = 2;
v___x_1804_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_1802_, v___x_1803_);
v___x_1805_ = lean_alloc_ctor(15, 4, 3);
lean_ctor_set(v___x_1805_, 0, v___f_1785_);
lean_ctor_set(v___x_1805_, 1, v___x_1789_);
lean_ctor_set(v___x_1805_, 2, v_a_1783_);
lean_ctor_set(v___x_1805_, 3, v_b_1784_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*4, v___x_1792_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*4 + 1, v___x_1795_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*4 + 2, v___x_1804_);
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object* v_00_u03c4_1806_, lean_object* v_a_1807_, lean_object* v_b_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Fmt_Doc_append___override___redArg(v_a_1807_, v_b_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___override___redArg(lean_object* v_x_1810_, uint8_t v_a_1811_){
_start:
{
if (lean_obj_tag(v_x_1810_) == 0)
{
uint8_t v___x_1812_; 
v___x_1812_ = 1;
return v___x_1812_;
}
else
{
lean_object* v_isFailure_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v_isFailure_1813_ = lean_ctor_get(v_x_1810_, 0);
lean_inc_ref(v_isFailure_1813_);
lean_dec(v_x_1810_);
v___x_1814_ = lean_box(v_a_1811_);
v___x_1815_ = lean_apply_1(v_isFailure_1813_, v___x_1814_);
v___x_1816_ = lean_unbox(v___x_1815_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___override___redArg___boxed(lean_object* v_x_1817_, lean_object* v_a_1818_){
_start:
{
uint8_t v_a_1581__boxed_1819_; uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_a_1581__boxed_1819_ = lean_unbox(v_a_1818_);
v_res_1820_ = l_Lean_Fmt_Doc_isFailure___override___redArg(v_x_1817_, v_a_1581__boxed_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___override(lean_object* v_00_u03c4_1822_, lean_object* v_x_1823_, uint8_t v_a_1824_){
_start:
{
uint8_t v___x_1825_; 
v___x_1825_ = l_Lean_Fmt_Doc_isFailure___override___redArg(v_x_1823_, v_a_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___override___boxed(lean_object* v_00_u03c4_1826_, lean_object* v_x_1827_, lean_object* v_a_1828_){
_start:
{
uint8_t v_a_1606__boxed_1829_; uint8_t v_res_1830_; lean_object* v_r_1831_; 
v_a_1606__boxed_1829_ = lean_unbox(v_a_1828_);
v_res_1830_ = l_Lean_Fmt_Doc_isFailure___override(v_00_u03c4_1826_, v_x_1827_, v_a_1606__boxed_1829_);
v_r_1831_ = lean_box(v_res_1830_);
return v_r_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object* v_00_u03c4_1832_, lean_object* v_x_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object* v_00_u03c4_1835_, lean_object* v_x_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(v_00_u03c4_1835_, v_x_1836_);
lean_dec(v_x_1836_);
return v_res_1837_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object* v_00_u03c4_1838_, lean_object* v_x_1839_){
_start:
{
uint8_t v___x_1840_; 
v___x_1840_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object* v_00_u03c4_1841_, lean_object* v_x_1842_){
_start:
{
uint8_t v_res_1843_; lean_object* v_r_1844_; 
v_res_1843_ = l_Lean_Fmt_Doc_alwaysEmptiness___override(v_00_u03c4_1841_, v_x_1842_);
lean_dec(v_x_1842_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object* v_00_u03c4_1845_, lean_object* v_x_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object* v_00_u03c4_1848_, lean_object* v_x_1849_){
_start:
{
uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_res_1850_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override(v_00_u03c4_1848_, v_x_1849_);
lean_dec(v_x_1849_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object* v_00_u03c4_1852_, lean_object* v_x_1853_){
_start:
{
uint8_t v___x_1854_; 
v___x_1854_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object* v_00_u03c4_1855_, lean_object* v_x_1856_){
_start:
{
uint8_t v_res_1857_; lean_object* v_r_1858_; 
v_res_1857_ = l_Lean_Fmt_Doc_atomicness___override(v_00_u03c4_1855_, v_x_1856_);
lean_dec(v_x_1856_);
v_r_1858_ = lean_box(v_res_1857_);
return v_r_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object* v_00_u03c4_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_box(0);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc(lean_object* v_a_1861_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_box(0);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_unsigned_to_nat(2u);
v___x_1867_ = lean_nat_to_int(v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_unsigned_to_nat(1u);
v___x_1869_ = lean_nat_to_int(v___x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg(lean_object* v_inst_1966_, lean_object* v_x_1967_, lean_object* v_prec_1968_){
_start:
{
lean_object* v___y_1970_; 
switch(lean_obj_tag(v_x_1967_))
{
case 0:
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
lean_dec_ref(v_inst_1966_);
v___x_1976_ = lean_unsigned_to_nat(1024u);
v___x_1977_ = lean_nat_dec_le(v___x_1976_, v_prec_1968_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1970_ = v___x_1978_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1970_ = v___x_1979_;
goto v___jp_1969_;
}
}
case 1:
{
lean_object* v_f_1980_; lean_object* v___y_1982_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
lean_dec_ref(v_inst_1966_);
v_f_1980_ = lean_ctor_get(v_x_1967_, 2);
lean_inc_ref(v_f_1980_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_1991_ = lean_unsigned_to_nat(1024u);
v___x_1992_ = lean_nat_dec_le(v___x_1991_, v_prec_1968_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1982_ = v___x_1993_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1982_ = v___x_1994_;
goto v___jp_1981_;
}
v___jp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1983_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__6));
v___x_1984_ = l_String_quote(v_f_1980_);
v___x_1985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1984_);
v___x_1986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1983_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
lean_inc(v___y_1982_);
v___x_1987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___y_1982_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = 0;
v___x_1989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*1, v___x_1988_);
v___x_1990_ = l_Repr_addAppParen(v___x_1989_, v_prec_1968_);
return v___x_1990_;
}
}
case 2:
{
lean_object* v_s_1995_; lean_object* v___y_1997_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
lean_dec_ref(v_inst_1966_);
v_s_1995_ = lean_ctor_get(v_x_1967_, 2);
lean_inc_ref(v_s_1995_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2006_ = lean_unsigned_to_nat(1024u);
v___x_2007_ = lean_nat_dec_le(v___x_2006_, v_prec_1968_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1997_ = v___x_2008_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1997_ = v___x_2009_;
goto v___jp_1996_;
}
v___jp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_1998_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__9));
v___x_1999_ = l_String_quote(v_s_1995_);
v___x_2000_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1998_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
lean_inc(v___y_1997_);
v___x_2002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___y_1997_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = 0;
v___x_2004_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*1, v___x_2003_);
v___x_2005_ = l_Repr_addAppParen(v___x_2004_, v_prec_1968_);
return v___x_2005_;
}
}
case 3:
{
lean_object* v_id_2010_; lean_object* v_d_2011_; lean_object* v___x_2012_; lean_object* v___y_2014_; uint8_t v___x_2027_; 
v_id_2010_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_id_2010_);
v_d_2011_ = lean_ctor_get(v_x_1967_, 3);
lean_inc(v_d_2011_);
lean_dec_ref_known(v_x_1967_, 4);
v___x_2012_ = lean_unsigned_to_nat(1024u);
v___x_2027_ = lean_nat_dec_le(v___x_2012_, v_prec_1968_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2014_ = v___x_2028_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2014_ = v___x_2029_;
goto v___jp_2013_;
}
v___jp_2013_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2015_ = lean_box(1);
v___x_2016_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__12));
v___x_2017_ = l_Nat_reprFast(v_id_2010_);
v___x_2018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
v___x_2019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2016_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v___x_2015_);
v___x_2021_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2011_, v___x_2012_);
v___x_2022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2020_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
lean_inc(v___y_2014_);
v___x_2023_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___y_2014_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = 0;
v___x_2025_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set_uint8(v___x_2025_, sizeof(void*)*1, v___x_2024_);
v___x_2026_ = l_Repr_addAppParen(v___x_2025_, v_prec_1968_);
return v___x_2026_;
}
}
case 4:
{
lean_object* v_d_2030_; lean_object* v___x_2031_; lean_object* v___y_2033_; uint8_t v___x_2041_; 
v_d_2030_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_d_2030_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2031_ = lean_unsigned_to_nat(1024u);
v___x_2041_ = lean_nat_dec_le(v___x_2031_, v_prec_1968_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2033_ = v___x_2042_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2033_ = v___x_2043_;
goto v___jp_2032_;
}
v___jp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2034_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__15));
v___x_2035_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2030_, v___x_2031_);
v___x_2036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
lean_inc(v___y_2033_);
v___x_2037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___y_2033_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = 0;
v___x_2039_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set_uint8(v___x_2039_, sizeof(void*)*1, v___x_2038_);
v___x_2040_ = l_Repr_addAppParen(v___x_2039_, v_prec_1968_);
return v___x_2040_;
}
}
case 5:
{
lean_object* v_d_2044_; lean_object* v___x_2045_; lean_object* v___y_2047_; uint8_t v___x_2055_; 
v_d_2044_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_d_2044_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2045_ = lean_unsigned_to_nat(1024u);
v___x_2055_ = lean_nat_dec_le(v___x_2045_, v_prec_1968_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2047_ = v___x_2056_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2047_ = v___x_2057_;
goto v___jp_2046_;
}
v___jp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2048_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__18));
v___x_2049_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2044_, v___x_2045_);
v___x_2050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
lean_inc(v___y_2047_);
v___x_2051_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___y_2047_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = 0;
v___x_2053_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*1, v___x_2052_);
v___x_2054_ = l_Repr_addAppParen(v___x_2053_, v_prec_1968_);
return v___x_2054_;
}
}
case 6:
{
lean_object* v_n_2058_; uint8_t v_isCumulative_2059_; lean_object* v_d_2060_; lean_object* v___x_2061_; lean_object* v___y_2063_; uint8_t v___x_2079_; 
v_n_2058_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_n_2058_);
v_isCumulative_2059_ = lean_ctor_get_uint8(v_x_1967_, sizeof(void*)*4 + 3);
v_d_2060_ = lean_ctor_get(v_x_1967_, 3);
lean_inc(v_d_2060_);
lean_dec_ref_known(v_x_1967_, 4);
v___x_2061_ = lean_unsigned_to_nat(1024u);
v___x_2079_ = lean_nat_dec_le(v___x_2061_, v_prec_1968_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2063_ = v___x_2080_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2063_ = v___x_2081_;
goto v___jp_2062_;
}
v___jp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2064_ = lean_box(1);
v___x_2065_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__21));
v___x_2066_ = l_Nat_reprFast(v_n_2058_);
v___x_2067_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2065_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v___x_2064_);
v___x_2070_ = l_Bool_repr___redArg(v_isCumulative_2059_);
v___x_2071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2064_);
v___x_2073_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2060_, v___x_2061_);
v___x_2074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
lean_inc(v___y_2063_);
v___x_2075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___y_2063_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = 0;
v___x_2077_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*1, v___x_2076_);
v___x_2078_ = l_Repr_addAppParen(v___x_2077_, v_prec_1968_);
return v___x_2078_;
}
}
case 7:
{
lean_object* v_d_2082_; lean_object* v___x_2083_; lean_object* v___y_2085_; uint8_t v___x_2093_; 
v_d_2082_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_d_2082_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2083_ = lean_unsigned_to_nat(1024u);
v___x_2093_ = lean_nat_dec_le(v___x_2083_, v_prec_1968_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2085_ = v___x_2094_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2095_; 
v___x_2095_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2085_ = v___x_2095_;
goto v___jp_2084_;
}
v___jp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2086_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__24));
v___x_2087_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2082_, v___x_2083_);
v___x_2088_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2086_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
lean_inc(v___y_2085_);
v___x_2089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___y_2085_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = 0;
v___x_2091_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set_uint8(v___x_2091_, sizeof(void*)*1, v___x_2090_);
v___x_2092_ = l_Repr_addAppParen(v___x_2091_, v_prec_1968_);
return v___x_2092_;
}
}
case 8:
{
uint8_t v_onlyNonCumulative_2096_; lean_object* v_d_2097_; lean_object* v___x_2098_; lean_object* v___y_2100_; uint8_t v___x_2112_; 
v_onlyNonCumulative_2096_ = lean_ctor_get_uint8(v_x_1967_, sizeof(void*)*3 + 3);
v_d_2097_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_d_2097_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2098_ = lean_unsigned_to_nat(1024u);
v___x_2112_ = lean_nat_dec_le(v___x_2098_, v_prec_1968_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2100_ = v___x_2113_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2100_ = v___x_2114_;
goto v___jp_2099_;
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2101_ = lean_box(1);
v___x_2102_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__27));
v___x_2103_ = l_Bool_repr___redArg(v_onlyNonCumulative_2096_);
v___x_2104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2101_);
v___x_2106_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2097_, v___x_2098_);
v___x_2107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
lean_inc(v___y_2100_);
v___x_2108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___y_2100_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = 0;
v___x_2110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set_uint8(v___x_2110_, sizeof(void*)*1, v___x_2109_);
v___x_2111_ = l_Repr_addAppParen(v___x_2110_, v_prec_1968_);
return v___x_2111_;
}
}
case 9:
{
lean_object* v_d_2115_; lean_object* v___x_2116_; lean_object* v___y_2118_; uint8_t v___x_2126_; 
v_d_2115_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_d_2115_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2116_ = lean_unsigned_to_nat(1024u);
v___x_2126_ = lean_nat_dec_le(v___x_2116_, v_prec_1968_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2118_ = v___x_2127_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2118_ = v___x_2128_;
goto v___jp_2117_;
}
v___jp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2119_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__30));
v___x_2120_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2115_, v___x_2116_);
v___x_2121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
lean_inc(v___y_2118_);
v___x_2122_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___y_2118_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = 0;
v___x_2124_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set_uint8(v___x_2124_, sizeof(void*)*1, v___x_2123_);
v___x_2125_ = l_Repr_addAppParen(v___x_2124_, v_prec_1968_);
return v___x_2125_;
}
}
case 10:
{
lean_object* v_d_2129_; lean_object* v___x_2130_; lean_object* v___y_2132_; uint8_t v___x_2140_; 
v_d_2129_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_d_2129_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2130_ = lean_unsigned_to_nat(1024u);
v___x_2140_ = lean_nat_dec_le(v___x_2130_, v_prec_1968_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2132_ = v___x_2141_;
goto v___jp_2131_;
}
else
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2132_ = v___x_2142_;
goto v___jp_2131_;
}
v___jp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2133_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__33));
v___x_2134_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2129_, v___x_2130_);
v___x_2135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
lean_inc(v___y_2132_);
v___x_2136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___y_2132_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = 0;
v___x_2138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*1, v___x_2137_);
v___x_2139_ = l_Repr_addAppParen(v___x_2138_, v_prec_1968_);
return v___x_2139_;
}
}
case 11:
{
lean_object* v_d_2143_; lean_object* v___x_2144_; lean_object* v___y_2146_; uint8_t v___x_2154_; 
v_d_2143_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_d_2143_);
lean_dec_ref_known(v_x_1967_, 3);
v___x_2144_ = lean_unsigned_to_nat(1024u);
v___x_2154_ = lean_nat_dec_le(v___x_2144_, v_prec_1968_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2146_ = v___x_2155_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2146_ = v___x_2156_;
goto v___jp_2145_;
}
v___jp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2147_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__36));
v___x_2148_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2143_, v___x_2144_);
v___x_2149_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
lean_inc(v___y_2146_);
v___x_2150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___y_2146_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = 0;
v___x_2152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*1, v___x_2151_);
v___x_2153_ = l_Repr_addAppParen(v___x_2152_, v_prec_1968_);
return v___x_2153_;
}
}
case 12:
{
lean_object* v_d_2157_; lean_object* v___x_2158_; lean_object* v___y_2160_; uint8_t v___x_2168_; 
v_d_2157_ = lean_ctor_get(v_x_1967_, 3);
lean_inc(v_d_2157_);
lean_dec_ref_known(v_x_1967_, 4);
v___x_2158_ = lean_unsigned_to_nat(1024u);
v___x_2168_ = lean_nat_dec_le(v___x_2158_, v_prec_1968_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2160_ = v___x_2169_;
goto v___jp_2159_;
}
else
{
lean_object* v___x_2170_; 
v___x_2170_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2160_ = v___x_2170_;
goto v___jp_2159_;
}
v___jp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2161_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__41));
v___x_2162_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2157_, v___x_2158_);
v___x_2163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
lean_inc(v___y_2160_);
v___x_2164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___y_2160_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = 0;
v___x_2166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*1, v___x_2165_);
v___x_2167_ = l_Repr_addAppParen(v___x_2166_, v_prec_1968_);
return v___x_2167_;
}
}
case 13:
{
lean_object* v_cost_2171_; lean_object* v_d_2172_; lean_object* v___x_2173_; lean_object* v___y_2175_; uint8_t v___x_2187_; 
v_cost_2171_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_cost_2171_);
v_d_2172_ = lean_ctor_get(v_x_1967_, 3);
lean_inc(v_d_2172_);
lean_dec_ref_known(v_x_1967_, 4);
v___x_2173_ = lean_unsigned_to_nat(1024u);
v___x_2187_ = lean_nat_dec_le(v___x_2173_, v_prec_1968_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2175_ = v___x_2188_;
goto v___jp_2174_;
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2175_ = v___x_2189_;
goto v___jp_2174_;
}
v___jp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2176_ = lean_box(1);
v___x_2177_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__44));
lean_inc_ref(v_inst_1966_);
v___x_2178_ = lean_apply_2(v_inst_1966_, v_cost_2171_, v___x_2173_);
v___x_2179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v___x_2176_);
v___x_2181_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_d_2172_, v___x_2173_);
v___x_2182_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2180_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
lean_inc(v___y_2175_);
v___x_2183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___y_2175_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = 0;
v___x_2185_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set_uint8(v___x_2185_, sizeof(void*)*1, v___x_2184_);
v___x_2186_ = l_Repr_addAppParen(v___x_2185_, v_prec_1968_);
return v___x_2186_;
}
}
case 14:
{
lean_object* v_a_2190_; lean_object* v_b_2191_; lean_object* v___x_2192_; lean_object* v___y_2194_; uint8_t v___x_2206_; 
v_a_2190_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_a_2190_);
v_b_2191_ = lean_ctor_get(v_x_1967_, 3);
lean_inc(v_b_2191_);
lean_dec_ref_known(v_x_1967_, 4);
v___x_2192_ = lean_unsigned_to_nat(1024u);
v___x_2206_ = lean_nat_dec_le(v___x_2192_, v_prec_1968_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2194_ = v___x_2207_;
goto v___jp_2193_;
}
else
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2194_ = v___x_2208_;
goto v___jp_2193_;
}
v___jp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2195_ = lean_box(1);
v___x_2196_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__47));
lean_inc_ref(v_inst_1966_);
v___x_2197_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_a_2190_, v___x_2192_);
v___x_2198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
lean_ctor_set(v___x_2199_, 1, v___x_2195_);
v___x_2200_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_b_2191_, v___x_2192_);
v___x_2201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_inc(v___y_2194_);
v___x_2202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___y_2194_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = 0;
v___x_2204_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set_uint8(v___x_2204_, sizeof(void*)*1, v___x_2203_);
v___x_2205_ = l_Repr_addAppParen(v___x_2204_, v_prec_1968_);
return v___x_2205_;
}
}
default: 
{
lean_object* v_a_2209_; lean_object* v_b_2210_; lean_object* v___x_2211_; lean_object* v___y_2213_; uint8_t v___x_2225_; 
v_a_2209_ = lean_ctor_get(v_x_1967_, 2);
lean_inc(v_a_2209_);
v_b_2210_ = lean_ctor_get(v_x_1967_, 3);
lean_inc(v_b_2210_);
lean_dec_ref_known(v_x_1967_, 4);
v___x_2211_ = lean_unsigned_to_nat(1024u);
v___x_2225_ = lean_nat_dec_le(v___x_2211_, v_prec_1968_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_2213_ = v___x_2226_;
goto v___jp_2212_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_2213_ = v___x_2227_;
goto v___jp_2212_;
}
v___jp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2214_ = lean_box(1);
v___x_2215_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__50));
lean_inc_ref(v_inst_1966_);
v___x_2216_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_a_2209_, v___x_2211_);
v___x_2217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2214_);
v___x_2219_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1966_, v_b_2210_, v___x_2211_);
v___x_2220_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
lean_inc(v___y_2213_);
v___x_2221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___y_2213_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = 0;
v___x_2223_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*1, v___x_2222_);
v___x_2224_ = l_Repr_addAppParen(v___x_2223_, v_prec_1968_);
return v___x_2224_;
}
}
}
v___jp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1971_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__1));
lean_inc(v___y_1970_);
v___x_1972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___y_1970_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = 0;
v___x_1974_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set_uint8(v___x_1974_, sizeof(void*)*1, v___x_1973_);
v___x_1975_ = l_Repr_addAppParen(v___x_1974_, v_prec_1968_);
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___boxed(lean_object* v_inst_2228_, lean_object* v_x_2229_, lean_object* v_prec_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2228_, v_x_2229_, v_prec_2230_);
lean_dec(v_prec_2230_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr(lean_object* v_00_u03c4_2232_, lean_object* v_inst_2233_, lean_object* v_x_2234_, lean_object* v_prec_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_2233_, v_x_2234_, v_prec_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___boxed(lean_object* v_00_u03c4_2237_, lean_object* v_inst_2238_, lean_object* v_x_2239_, lean_object* v_prec_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Fmt_instReprDoc_repr(v_00_u03c4_2237_, v_inst_2238_, v_x_2239_, v_prec_2240_);
lean_dec(v_prec_2240_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc___redArg(lean_object* v_inst_2242_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2243_, 0, lean_box(0));
lean_closure_set(v___x_2243_, 1, v_inst_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc(lean_object* v_00_u03c4_2244_, lean_object* v_inst_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2246_, 0, lean_box(0));
lean_closure_set(v___x_2246_, 1, v_inst_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object* v_d_2247_){
_start:
{
uint8_t v___x_2248_; 
v___x_2248_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2247_);
if (v___x_2248_ == 0)
{
uint8_t v___x_2249_; 
v___x_2249_ = 1;
return v___x_2249_;
}
else
{
uint8_t v___x_2250_; 
v___x_2250_ = 0;
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___redArg___boxed(lean_object* v_d_2251_){
_start:
{
uint8_t v_res_2252_; lean_object* v_r_2253_; 
v_res_2252_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_2251_);
lean_dec(v_d_2251_);
v_r_2253_ = lean_box(v_res_2252_);
return v_r_2253_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty(lean_object* v_00_u03c4_2254_, lean_object* v_d_2255_){
_start:
{
uint8_t v___x_2256_; 
v___x_2256_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___boxed(lean_object* v_00_u03c4_2257_, lean_object* v_d_2258_){
_start:
{
uint8_t v_res_2259_; lean_object* v_r_2260_; 
v_res_2259_ = l_Lean_Fmt_Doc_isAlwaysEmpty(v_00_u03c4_2257_, v_d_2258_);
lean_dec(v_d_2258_);
v_r_2260_ = lean_box(v_res_2259_);
return v_r_2260_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object* v_d_2261_){
_start:
{
uint8_t v___x_2262_; 
v___x_2262_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2261_);
if (v___x_2262_ == 0)
{
uint8_t v___x_2263_; 
v___x_2263_ = 1;
return v___x_2263_;
}
else
{
uint8_t v___x_2264_; 
v___x_2264_ = 0;
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg___boxed(lean_object* v_d_2265_){
_start:
{
uint8_t v_res_2266_; lean_object* v_r_2267_; 
v_res_2266_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_2265_);
lean_dec(v_d_2265_);
v_r_2267_ = lean_box(v_res_2266_);
return v_r_2267_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty(lean_object* v_00_u03c4_2268_, lean_object* v_d_2269_){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___boxed(lean_object* v_00_u03c4_2271_, lean_object* v_d_2272_){
_start:
{
uint8_t v_res_2273_; lean_object* v_r_2274_; 
v_res_2273_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty(v_00_u03c4_2271_, v_d_2272_);
lean_dec(v_d_2272_);
v_r_2274_ = lean_box(v_res_2273_);
return v_r_2274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object* v_d_2275_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2275_);
if (v___x_2276_ == 2)
{
uint8_t v___x_2277_; 
v___x_2277_ = 1;
return v___x_2277_;
}
else
{
if (v___x_2276_ == 0)
{
uint8_t v___x_2278_; 
v___x_2278_ = 1;
return v___x_2278_;
}
else
{
uint8_t v___x_2279_; 
v___x_2279_ = 0;
return v___x_2279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___redArg___boxed(lean_object* v_d_2280_){
_start:
{
uint8_t v_res_2281_; lean_object* v_r_2282_; 
v_res_2281_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_2280_);
lean_dec(v_d_2280_);
v_r_2282_ = lean_box(v_res_2281_);
return v_r_2282_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic(lean_object* v_00_u03c4_2283_, lean_object* v_d_2284_){
_start:
{
uint8_t v___x_2285_; 
v___x_2285_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___boxed(lean_object* v_00_u03c4_2286_, lean_object* v_d_2287_){
_start:
{
uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_res_2288_ = l_Lean_Fmt_Doc_isCompoundAtomic(v_00_u03c4_2286_, v_d_2287_);
lean_dec(v_d_2287_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object* v_d_2290_){
_start:
{
uint8_t v___x_2291_; 
v___x_2291_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2290_);
if (v___x_2291_ == 0)
{
uint8_t v___x_2292_; 
v___x_2292_ = 1;
return v___x_2292_;
}
else
{
uint8_t v___x_2293_; 
v___x_2293_ = 0;
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___redArg___boxed(lean_object* v_d_2294_){
_start:
{
uint8_t v_res_2295_; lean_object* v_r_2296_; 
v_res_2295_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_2294_);
lean_dec(v_d_2294_);
v_r_2296_ = lean_box(v_res_2295_);
return v_r_2296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic(lean_object* v_00_u03c4_2297_, lean_object* v_d_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___boxed(lean_object* v_00_u03c4_2300_, lean_object* v_d_2301_){
_start:
{
uint8_t v_res_2302_; lean_object* v_r_2303_; 
v_res_2302_ = l_Lean_Fmt_Doc_isAtomic(v_00_u03c4_2300_, v_d_2301_);
lean_dec(v_d_2301_);
v_r_2303_ = lean_box(v_res_2302_);
return v_r_2303_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___closed__1(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___closed__0));
v___x_2306_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object* v_00_u03c4_2307_){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__1, &l_Lean_Fmt_Doc_empty___closed__1_once, _init_l_Lean_Fmt_Doc_empty___closed__1);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object* v_d_2309_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_inc(v_d_2309_);
v___x_2310_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_2309_);
v___x_2311_ = l_Lean_Fmt_Doc_either___override___redArg(v_d_2309_, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object* v_00_u03c4_2312_, lean_object* v_d_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_Fmt_Doc_maybeFlattened___redArg(v_d_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___closed__1(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___closed__0));
v___x_2317_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object* v_00_u03c4_2318_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__1, &l_Lean_Fmt_Doc_nl___closed__1_once, _init_l_Lean_Fmt_Doc_nl___closed__1);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___closed__0(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___closed__0));
v___x_2321_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object* v_00_u03c4_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = lean_obj_once(&l_Lean_Fmt_Doc_break___closed__0, &l_Lean_Fmt_Doc_break___closed__0_once, _init_l_Lean_Fmt_Doc_break___closed__0);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_Fmt_Doc_nl(lean_box(0));
return v___x_2324_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___closed__1(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_2326_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object* v_00_u03c4_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__1, &l_Lean_Fmt_Doc_hardNl___closed__1_once, _init_l_Lean_Fmt_Doc_hardNl___closed__1);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object* v_d_2329_){
_start:
{
lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = lean_unsigned_to_nat(2u);
v___x_2331_ = 0;
v___x_2332_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_2330_, v___x_2331_, v_d_2329_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object* v_00_u03c4_2333_, lean_object* v_d_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Fmt_Doc_nested___redArg(v_d_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object* v_d_2336_){
_start:
{
lean_object* v___x_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_unsigned_to_nat(2u);
v___x_2338_ = 1;
v___x_2339_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_2337_, v___x_2338_, v_d_2336_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object* v_00_u03c4_2340_, lean_object* v_d_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Fmt_Doc_hardNested___redArg(v_d_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object* v_a_2343_, lean_object* v_b_2344_){
_start:
{
lean_object* v_array_2345_; lean_object* v_start_2346_; lean_object* v_stop_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2360_; 
v_array_2345_ = lean_ctor_get(v_a_2343_, 0);
v_start_2346_ = lean_ctor_get(v_a_2343_, 1);
v_stop_2347_ = lean_ctor_get(v_a_2343_, 2);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_a_2343_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2349_ = v_a_2343_;
v_isShared_2350_ = v_isSharedCheck_2360_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_stop_2347_);
lean_inc(v_start_2346_);
lean_inc(v_array_2345_);
lean_dec(v_a_2343_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2360_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_nat_dec_lt(v_start_2346_, v_stop_2347_);
if (v___x_2351_ == 0)
{
lean_del_object(v___x_2349_);
lean_dec(v_stop_2347_);
lean_dec(v_start_2346_);
lean_dec_ref(v_array_2345_);
return v_b_2344_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_nat_add(v_start_2346_, v___x_2352_);
lean_inc_ref(v_array_2345_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 1, v___x_2353_);
v___x_2355_ = v___x_2349_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_array_2345_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_stop_2347_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_array_fget(v_array_2345_, v_start_2346_);
lean_dec(v_start_2346_);
lean_dec_ref(v_array_2345_);
v___x_2357_ = l_Lean_Fmt_Doc_either___override___redArg(v_b_2344_, v___x_2356_);
v_a_2343_ = v___x_2355_;
v_b_2344_ = v___x_2357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object* v_ds_2361_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = lean_array_get_size(v_ds_2361_);
v___x_2364_ = lean_nat_dec_lt(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec_ref(v_ds_2361_);
v___x_2365_ = lean_box(0);
return v___x_2365_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2366_ = lean_array_fget(v_ds_2361_, v___x_2362_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = l_Array_toSubarray___redArg(v_ds_2361_, v___x_2367_, v___x_2363_);
v___x_2369_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v___x_2368_, v___x_2366_);
return v___x_2369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object* v_00_u03c4_2370_, lean_object* v_ds_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Fmt_Doc_oneOf___redArg(v_ds_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object* v_00_u03c4_2373_, lean_object* v_inst_2374_, lean_object* v_R_2375_, lean_object* v_a_2376_, lean_object* v_b_2377_, lean_object* v_c_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v_a_2376_, v_b_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc___lam__0(lean_object* v_d1_2380_, lean_object* v_d2_2381_){
_start:
{
uint8_t v___x_2382_; 
v___x_2382_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d1_2380_);
if (v___x_2382_ == 0)
{
uint8_t v___x_2383_; 
v___x_2383_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d2_2381_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; 
v___x_2384_ = l_Lean_Fmt_Doc_append___override___redArg(v_d1_2380_, v_d2_2381_);
return v___x_2384_;
}
else
{
lean_dec(v_d2_2381_);
return v_d1_2380_;
}
}
else
{
lean_dec(v_d1_2380_);
return v_d2_2381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object* v_00_u03c4_2386_){
_start:
{
lean_object* v___f_2387_; 
v___f_2387_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___closed__0));
return v___f_2387_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object* v_a_2388_, lean_object* v_b_2389_){
_start:
{
lean_object* v_array_2390_; lean_object* v_start_2391_; lean_object* v_stop_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2409_; 
v_array_2390_ = lean_ctor_get(v_a_2388_, 0);
v_start_2391_ = lean_ctor_get(v_a_2388_, 1);
v_stop_2392_ = lean_ctor_get(v_a_2388_, 2);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_a_2388_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2394_ = v_a_2388_;
v_isShared_2395_ = v_isSharedCheck_2409_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_stop_2392_);
lean_inc(v_start_2391_);
lean_inc(v_array_2390_);
lean_dec(v_a_2388_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2409_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
uint8_t v___x_2396_; 
v___x_2396_ = lean_nat_dec_lt(v_start_2391_, v_stop_2392_);
if (v___x_2396_ == 0)
{
lean_del_object(v___x_2394_);
lean_dec(v_stop_2392_);
lean_dec(v_start_2391_);
lean_dec_ref(v_array_2390_);
return v_b_2389_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_add(v_start_2391_, v___x_2397_);
lean_inc_ref(v_array_2390_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v___x_2398_);
v___x_2400_ = v___x_2394_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_array_2390_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_stop_2392_);
v___x_2400_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2401_ = lean_array_fget(v_array_2390_, v_start_2391_);
lean_dec(v_start_2391_);
lean_dec_ref(v_array_2390_);
v___x_2402_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_2389_);
if (v___x_2402_ == 0)
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_2401_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_2389_, v___x_2401_);
v_a_2388_ = v___x_2400_;
v_b_2389_ = v___x_2404_;
goto _start;
}
else
{
lean_dec(v___x_2401_);
v_a_2388_ = v___x_2400_;
goto _start;
}
}
else
{
lean_dec(v_b_2389_);
v_a_2388_ = v___x_2400_;
v_b_2389_ = v___x_2401_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object* v_ds_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = lean_array_get_size(v_ds_2410_);
v___x_2413_ = lean_nat_dec_lt(v___x_2411_, v___x_2412_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; 
lean_dec_ref(v_ds_2410_);
v___x_2414_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__1, &l_Lean_Fmt_Doc_empty___closed__1_once, _init_l_Lean_Fmt_Doc_empty___closed__1);
return v___x_2414_;
}
else
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = lean_array_fget(v_ds_2410_, v___x_2411_);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = l_Array_toSubarray___redArg(v_ds_2410_, v___x_2416_, v___x_2412_);
v___x_2418_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v___x_2417_, v___x_2415_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object* v_00_u03c4_2419_, lean_object* v_ds_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_Fmt_Doc_join___redArg(v_ds_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object* v_00_u03c4_2422_, lean_object* v_inst_2423_, lean_object* v_R_2424_, lean_object* v_a_2425_, lean_object* v_b_2426_, lean_object* v_c_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v_a_2425_, v_b_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object* v_sep_2429_, lean_object* v_a_2430_, lean_object* v_b_2431_){
_start:
{
lean_object* v_array_2432_; lean_object* v_start_2433_; lean_object* v_stop_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2456_; 
v_array_2432_ = lean_ctor_get(v_a_2430_, 0);
v_start_2433_ = lean_ctor_get(v_a_2430_, 1);
v_stop_2434_ = lean_ctor_get(v_a_2430_, 2);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_a_2430_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2436_ = v_a_2430_;
v_isShared_2437_ = v_isSharedCheck_2456_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_stop_2434_);
lean_inc(v_start_2433_);
lean_inc(v_array_2432_);
lean_dec(v_a_2430_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2456_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_nat_dec_lt(v_start_2433_, v_stop_2434_);
if (v___x_2438_ == 0)
{
lean_del_object(v___x_2436_);
lean_dec(v_stop_2434_);
lean_dec(v_start_2433_);
lean_dec_ref(v_array_2432_);
lean_dec(v_sep_2429_);
return v_b_2431_;
}
else
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = lean_nat_add(v_start_2433_, v___x_2439_);
lean_inc_ref(v_array_2432_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 1, v___x_2440_);
v___x_2442_ = v___x_2436_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_array_2432_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_stop_2434_);
v___x_2442_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___y_2445_; uint8_t v___x_2452_; 
v___x_2443_ = lean_array_fget(v_array_2432_, v_start_2433_);
lean_dec(v_start_2433_);
lean_dec_ref(v_array_2432_);
v___x_2452_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_b_2431_);
if (v___x_2452_ == 0)
{
uint8_t v___x_2453_; 
v___x_2453_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_sep_2429_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_inc(v_sep_2429_);
v___x_2454_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_2431_, v_sep_2429_);
v___y_2445_ = v___x_2454_;
goto v___jp_2444_;
}
else
{
v___y_2445_ = v_b_2431_;
goto v___jp_2444_;
}
}
else
{
lean_dec(v_b_2431_);
lean_inc(v_sep_2429_);
v___y_2445_ = v_sep_2429_;
goto v___jp_2444_;
}
v___jp_2444_:
{
uint8_t v___x_2446_; 
v___x_2446_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___y_2445_);
if (v___x_2446_ == 0)
{
uint8_t v___x_2447_; 
v___x_2447_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v___x_2443_);
if (v___x_2447_ == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Fmt_Doc_append___override___redArg(v___y_2445_, v___x_2443_);
v_a_2430_ = v___x_2442_;
v_b_2431_ = v___x_2448_;
goto _start;
}
else
{
lean_dec(v___x_2443_);
v_a_2430_ = v___x_2442_;
v_b_2431_ = v___y_2445_;
goto _start;
}
}
else
{
lean_dec(v___y_2445_);
v_a_2430_ = v___x_2442_;
v_b_2431_ = v___x_2443_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object* v_sep_2457_, lean_object* v_ds_2458_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2459_ = lean_unsigned_to_nat(0u);
v___x_2460_ = lean_array_get_size(v_ds_2458_);
v___x_2461_ = lean_nat_dec_lt(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
lean_dec_ref(v_ds_2458_);
lean_dec(v_sep_2457_);
v___x_2462_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__1, &l_Lean_Fmt_Doc_empty___closed__1_once, _init_l_Lean_Fmt_Doc_empty___closed__1);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2463_ = lean_array_fget(v_ds_2458_, v___x_2459_);
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2465_ = l_Array_toSubarray___redArg(v_ds_2458_, v___x_2464_, v___x_2460_);
v___x_2466_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_2457_, v___x_2465_, v___x_2463_);
return v___x_2466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object* v_00_u03c4_2467_, lean_object* v_sep_2468_, lean_object* v_ds_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_sep_2468_, v_ds_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object* v_00_u03c4_2471_, lean_object* v_sep_2472_, lean_object* v_inst_2473_, lean_object* v_R_2474_, lean_object* v_a_2475_, lean_object* v_b_2476_, lean_object* v_c_2477_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_2472_, v_a_2475_, v_b_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_Fmt_Doc_hardNl(lean_box(0));
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(lean_object* v_a_2480_, lean_object* v_b_2481_){
_start:
{
lean_object* v_array_2482_; lean_object* v_start_2483_; lean_object* v_stop_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2525_; 
v_array_2482_ = lean_ctor_get(v_a_2480_, 0);
v_start_2483_ = lean_ctor_get(v_a_2480_, 1);
v_stop_2484_ = lean_ctor_get(v_a_2480_, 2);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_a_2480_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2486_ = v_a_2480_;
v_isShared_2487_ = v_isSharedCheck_2525_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_stop_2484_);
lean_inc(v_start_2483_);
lean_inc(v_array_2482_);
lean_dec(v_a_2480_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2525_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
uint8_t v___x_2488_; 
v___x_2488_ = lean_nat_dec_lt(v_start_2483_, v_stop_2484_);
if (v___x_2488_ == 0)
{
lean_del_object(v___x_2486_);
lean_dec(v_stop_2484_);
lean_dec(v_start_2483_);
lean_dec_ref(v_array_2482_);
return v_b_2481_;
}
else
{
lean_object* v_fst_2489_; lean_object* v_snd_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2524_; 
v_fst_2489_ = lean_ctor_get(v_b_2481_, 0);
v_snd_2490_ = lean_ctor_get(v_b_2481_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_b_2481_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2492_ = v_b_2481_;
v_isShared_2493_ = v_isSharedCheck_2524_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_snd_2490_);
lean_inc(v_fst_2489_);
lean_dec(v_b_2481_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2524_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2494_ = lean_unsigned_to_nat(1u);
v___x_2495_ = lean_nat_add(v_start_2483_, v___x_2494_);
lean_inc_ref(v_array_2482_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 1, v___x_2495_);
v___x_2497_ = v___x_2486_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_array_2482_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_stop_2484_);
v___x_2497_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2498_ = lean_array_fget(v_array_2482_, v_start_2483_);
lean_dec(v_start_2483_);
lean_dec_ref(v_array_2482_);
v___x_2499_ = lean_unsigned_to_nat(2u);
v___x_2500_ = lean_mk_empty_array_with_capacity(v___x_2499_);
lean_inc_ref(v___x_2500_);
v___x_2501_ = lean_array_push(v___x_2500_, v_fst_2489_);
lean_inc_ref(v___x_2501_);
v___x_2502_ = lean_array_push(v___x_2501_, v_snd_2490_);
v___x_2503_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2502_);
lean_inc(v___x_2498_);
v___x_2504_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_2498_);
lean_inc(v___x_2504_);
v___x_2505_ = lean_array_push(v___x_2501_, v___x_2504_);
v___x_2506_ = l_Lean_Fmt_Doc_join___redArg(v___x_2505_);
v___x_2507_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2508_ = lean_unsigned_to_nat(3u);
v___x_2509_ = lean_mk_empty_array_with_capacity(v___x_2508_);
v___x_2510_ = lean_array_push(v___x_2509_, v___x_2503_);
v___x_2511_ = lean_array_push(v___x_2510_, v___x_2507_);
lean_inc_ref(v___x_2511_);
v___x_2512_ = lean_array_push(v___x_2511_, v___x_2504_);
v___x_2513_ = l_Lean_Fmt_Doc_join___redArg(v___x_2512_);
v___x_2514_ = lean_array_push(v___x_2500_, v___x_2506_);
v___x_2515_ = lean_array_push(v___x_2514_, v___x_2513_);
v___x_2516_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2515_);
v___x_2517_ = lean_array_push(v___x_2511_, v___x_2498_);
v___x_2518_ = l_Lean_Fmt_Doc_join___redArg(v___x_2517_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2518_);
lean_ctor_set(v___x_2492_, 0, v___x_2516_);
v___x_2520_ = v___x_2492_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
v_a_2480_ = v___x_2497_;
v_b_2481_ = v___x_2520_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fill___redArg___closed__0(void){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_Fmt_Doc_empty(lean_box(0));
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object* v_ds_2527_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2528_ = lean_array_get_size(v_ds_2527_);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = lean_nat_dec_eq(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v_lastNotFlattened_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2531_ = lean_box(0);
v_lastNotFlattened_2532_ = lean_array_get(v___x_2531_, v_ds_2527_, v___x_2529_);
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = lean_nat_dec_eq(v___x_2528_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_object* v_lastFlattened_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_inc(v_lastNotFlattened_2532_);
v_lastFlattened_2535_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_2532_);
v___x_2536_ = l_Array_toSubarray___redArg(v_ds_2527_, v___x_2533_, v___x_2528_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_lastFlattened_2535_);
lean_ctor_set(v___x_2537_, 1, v_lastNotFlattened_2532_);
v___x_2538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(v___x_2536_, v___x_2537_);
v_fst_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_fst_2539_);
v_snd_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_snd_2540_);
lean_dec_ref(v___x_2538_);
v___x_2541_ = lean_unsigned_to_nat(2u);
v___x_2542_ = lean_mk_empty_array_with_capacity(v___x_2541_);
v___x_2543_ = lean_array_push(v___x_2542_, v_fst_2539_);
v___x_2544_ = lean_array_push(v___x_2543_, v_snd_2540_);
v___x_2545_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2544_);
return v___x_2545_;
}
else
{
lean_dec_ref(v_ds_2527_);
return v_lastNotFlattened_2532_;
}
}
else
{
lean_object* v___x_2546_; 
lean_dec_ref(v_ds_2527_);
v___x_2546_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill(lean_object* v_00_u03c4_2547_, lean_object* v_ds_2548_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_Fmt_Doc_fill___redArg(v_ds_2548_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0(lean_object* v_00_u03c4_2550_, lean_object* v_inst_2551_, lean_object* v_R_2552_, lean_object* v_a_2553_, lean_object* v_b_2554_, lean_object* v_c_2555_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(v_a_2553_, v_b_2554_);
return v___x_2556_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2557_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2558_ = lean_unsigned_to_nat(2u);
v___x_2559_ = lean_mk_empty_array_with_capacity(v___x_2558_);
v___x_2560_ = lean_array_push(v___x_2559_, v___x_2557_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(lean_object* v_wrap_2561_, lean_object* v_as_2562_, size_t v_sz_2563_, size_t v_i_2564_, lean_object* v_b_2565_){
_start:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_usize_dec_lt(v_i_2564_, v_sz_2563_);
if (v___x_2566_ == 0)
{
lean_dec_ref(v_wrap_2561_);
return v_b_2565_;
}
else
{
lean_object* v_fst_2567_; lean_object* v_snd_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2601_; 
v_fst_2567_ = lean_ctor_get(v_b_2565_, 0);
v_snd_2568_ = lean_ctor_get(v_b_2565_, 1);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_b_2565_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2570_ = v_b_2565_;
v_isShared_2571_ = v_isSharedCheck_2601_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snd_2568_);
lean_inc(v_fst_2567_);
lean_dec(v_b_2565_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2601_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_a_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v_a_2572_ = lean_array_uget_borrowed(v_as_2562_, v_i_2564_);
v___x_2573_ = lean_unsigned_to_nat(2u);
v___x_2574_ = lean_mk_empty_array_with_capacity(v___x_2573_);
lean_inc(v_fst_2567_);
lean_inc_ref_n(v___x_2574_, 3);
v___x_2575_ = lean_array_push(v___x_2574_, v_fst_2567_);
v___x_2576_ = lean_array_push(v___x_2575_, v_snd_2568_);
v___x_2577_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2576_);
v___x_2578_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_2579_ = lean_array_push(v___x_2578_, v___x_2577_);
v___x_2580_ = l_Lean_Fmt_Doc_join___redArg(v___x_2579_);
lean_inc_ref_n(v_wrap_2561_, 2);
v___x_2581_ = lean_apply_1(v_wrap_2561_, v___x_2580_);
lean_inc_n(v_a_2572_, 2);
v___x_2582_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_a_2572_);
v___x_2583_ = lean_apply_1(v_wrap_2561_, v_fst_2567_);
v___x_2584_ = lean_array_push(v___x_2574_, v___x_2582_);
lean_inc_ref(v___x_2584_);
v___x_2585_ = lean_array_push(v___x_2584_, v___x_2583_);
v___x_2586_ = l_Lean_Fmt_Doc_join___redArg(v___x_2585_);
lean_inc(v___x_2581_);
v___x_2587_ = lean_array_push(v___x_2584_, v___x_2581_);
v___x_2588_ = l_Lean_Fmt_Doc_join___redArg(v___x_2587_);
v___x_2589_ = lean_array_push(v___x_2574_, v___x_2586_);
v___x_2590_ = lean_array_push(v___x_2589_, v___x_2588_);
v___x_2591_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2590_);
v___x_2592_ = lean_array_push(v___x_2574_, v_a_2572_);
v___x_2593_ = lean_array_push(v___x_2592_, v___x_2581_);
v___x_2594_ = l_Lean_Fmt_Doc_join___redArg(v___x_2593_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2594_);
lean_ctor_set(v___x_2570_, 0, v___x_2591_);
v___x_2596_ = v___x_2570_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
size_t v___x_2597_; size_t v___x_2598_; 
v___x_2597_ = ((size_t)1ULL);
v___x_2598_ = lean_usize_add(v_i_2564_, v___x_2597_);
v_i_2564_ = v___x_2598_;
v_b_2565_ = v___x_2596_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___boxed(lean_object* v_wrap_2602_, lean_object* v_as_2603_, lean_object* v_sz_2604_, lean_object* v_i_2605_, lean_object* v_b_2606_){
_start:
{
size_t v_sz_boxed_2607_; size_t v_i_boxed_2608_; lean_object* v_res_2609_; 
v_sz_boxed_2607_ = lean_unbox_usize(v_sz_2604_);
lean_dec(v_sz_2604_);
v_i_boxed_2608_ = lean_unbox_usize(v_i_2605_);
lean_dec(v_i_2605_);
v_res_2609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_2602_, v_as_2603_, v_sz_boxed_2607_, v_i_boxed_2608_, v_b_2606_);
lean_dec_ref(v_as_2603_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object* v_ds_2610_, lean_object* v_wrap_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2612_ = lean_array_get_size(v_ds_2610_);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_nat_dec_eq(v___x_2612_, v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_restNotFlattened_2618_; uint8_t v___x_2619_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_sub(v___x_2612_, v___x_2616_);
v_restNotFlattened_2618_ = lean_array_get(v___x_2615_, v_ds_2610_, v___x_2617_);
lean_dec(v___x_2617_);
v___x_2619_ = lean_nat_dec_eq(v___x_2612_, v___x_2616_);
if (v___x_2619_ == 0)
{
lean_object* v_restFlattened_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; size_t v_sz_2624_; size_t v___x_2625_; lean_object* v___x_2626_; lean_object* v_fst_2627_; lean_object* v_snd_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_inc(v_restNotFlattened_2618_);
v_restFlattened_2620_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_2618_);
v___x_2621_ = lean_array_pop(v_ds_2610_);
v___x_2622_ = l_Array_reverse___redArg(v___x_2621_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_restFlattened_2620_);
lean_ctor_set(v___x_2623_, 1, v_restNotFlattened_2618_);
v_sz_2624_ = lean_array_size(v___x_2622_);
v___x_2625_ = ((size_t)0ULL);
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_2611_, v___x_2622_, v_sz_2624_, v___x_2625_, v___x_2623_);
lean_dec_ref(v___x_2622_);
v_fst_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_fst_2627_);
v_snd_2628_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_snd_2628_);
lean_dec_ref(v___x_2626_);
v___x_2629_ = lean_unsigned_to_nat(2u);
v___x_2630_ = lean_mk_empty_array_with_capacity(v___x_2629_);
v___x_2631_ = lean_array_push(v___x_2630_, v_fst_2627_);
v___x_2632_ = lean_array_push(v___x_2631_, v_snd_2628_);
v___x_2633_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2632_);
return v___x_2633_;
}
else
{
lean_dec_ref(v_wrap_2611_);
lean_dec_ref(v_ds_2610_);
return v_restNotFlattened_2618_;
}
}
else
{
lean_object* v___x_2634_; 
lean_dec_ref(v_wrap_2611_);
lean_dec_ref(v_ds_2610_);
v___x_2634_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping(lean_object* v_00_u03c4_2635_, lean_object* v_ds_2636_, lean_object* v_wrap_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_ds_2636_, v_wrap_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0(lean_object* v_00_u03c4_2639_, lean_object* v_wrap_2640_, lean_object* v_as_2641_, size_t v_sz_2642_, size_t v_i_2643_, lean_object* v_b_2644_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_2640_, v_as_2641_, v_sz_2642_, v_i_2643_, v_b_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___boxed(lean_object* v_00_u03c4_2646_, lean_object* v_wrap_2647_, lean_object* v_as_2648_, lean_object* v_sz_2649_, lean_object* v_i_2650_, lean_object* v_b_2651_){
_start:
{
size_t v_sz_boxed_2652_; size_t v_i_boxed_2653_; lean_object* v_res_2654_; 
v_sz_boxed_2652_ = lean_unbox_usize(v_sz_2649_);
lean_dec(v_sz_2649_);
v_i_boxed_2653_ = lean_unbox_usize(v_i_2650_);
lean_dec(v_i_2650_);
v_res_2654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0(v_00_u03c4_2646_, v_wrap_2647_, v_as_2648_, v_sz_boxed_2652_, v_i_boxed_2653_, v_b_2651_);
lean_dec_ref(v_as_2648_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(lean_object* v_sep_2655_, lean_object* v_a_2656_, lean_object* v_b_2657_){
_start:
{
lean_object* v_array_2658_; lean_object* v_start_2659_; lean_object* v_stop_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2706_; 
v_array_2658_ = lean_ctor_get(v_a_2656_, 0);
v_start_2659_ = lean_ctor_get(v_a_2656_, 1);
v_stop_2660_ = lean_ctor_get(v_a_2656_, 2);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_a_2656_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2662_ = v_a_2656_;
v_isShared_2663_ = v_isSharedCheck_2706_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_stop_2660_);
lean_inc(v_start_2659_);
lean_inc(v_array_2658_);
lean_dec(v_a_2656_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2706_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint8_t v___x_2664_; 
v___x_2664_ = lean_nat_dec_lt(v_start_2659_, v_stop_2660_);
if (v___x_2664_ == 0)
{
lean_del_object(v___x_2662_);
lean_dec(v_stop_2660_);
lean_dec(v_start_2659_);
lean_dec_ref(v_array_2658_);
lean_dec(v_sep_2655_);
return v_b_2657_;
}
else
{
lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2705_; 
v_fst_2665_ = lean_ctor_get(v_b_2657_, 0);
v_snd_2666_ = lean_ctor_get(v_b_2657_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_b_2657_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2668_ = v_b_2657_;
v_isShared_2669_ = v_isSharedCheck_2705_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snd_2666_);
lean_inc(v_fst_2665_);
lean_dec(v_b_2657_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2705_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = lean_unsigned_to_nat(1u);
v___x_2671_ = lean_nat_add(v_start_2659_, v___x_2670_);
lean_inc_ref(v_array_2658_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 1, v___x_2671_);
v___x_2673_ = v___x_2662_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_array_2658_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_stop_2660_);
v___x_2673_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2674_ = lean_array_fget(v_array_2658_, v_start_2659_);
lean_dec(v_start_2659_);
lean_dec_ref(v_array_2658_);
v___x_2675_ = lean_unsigned_to_nat(2u);
v___x_2676_ = lean_mk_empty_array_with_capacity(v___x_2675_);
lean_inc(v_fst_2665_);
lean_inc_ref(v___x_2676_);
v___x_2677_ = lean_array_push(v___x_2676_, v_fst_2665_);
v___x_2678_ = lean_array_push(v___x_2677_, v_snd_2666_);
v___x_2679_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2678_);
lean_inc(v___x_2674_);
v___x_2680_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_2674_);
v___x_2681_ = lean_unsigned_to_nat(3u);
v___x_2682_ = lean_mk_empty_array_with_capacity(v___x_2681_);
v___x_2683_ = lean_array_push(v___x_2682_, v_fst_2665_);
lean_inc_n(v_sep_2655_, 2);
v___x_2684_ = lean_array_push(v___x_2683_, v_sep_2655_);
lean_inc(v___x_2680_);
v___x_2685_ = lean_array_push(v___x_2684_, v___x_2680_);
v___x_2686_ = l_Lean_Fmt_Doc_join___redArg(v___x_2685_);
v___x_2687_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2688_ = lean_unsigned_to_nat(4u);
v___x_2689_ = lean_mk_empty_array_with_capacity(v___x_2688_);
v___x_2690_ = lean_array_push(v___x_2689_, v___x_2679_);
v___x_2691_ = lean_array_push(v___x_2690_, v_sep_2655_);
v___x_2692_ = lean_array_push(v___x_2691_, v___x_2687_);
lean_inc_ref(v___x_2692_);
v___x_2693_ = lean_array_push(v___x_2692_, v___x_2680_);
v___x_2694_ = l_Lean_Fmt_Doc_join___redArg(v___x_2693_);
v___x_2695_ = lean_array_push(v___x_2676_, v___x_2686_);
v___x_2696_ = lean_array_push(v___x_2695_, v___x_2694_);
v___x_2697_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2696_);
v___x_2698_ = lean_array_push(v___x_2692_, v___x_2674_);
v___x_2699_ = l_Lean_Fmt_Doc_join___redArg(v___x_2698_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2699_);
lean_ctor_set(v___x_2668_, 0, v___x_2697_);
v___x_2701_ = v___x_2668_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2703_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
v_a_2656_ = v___x_2673_;
v_b_2657_ = v___x_2701_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object* v_sep_2707_, lean_object* v_ds_2708_){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2709_ = lean_array_get_size(v_ds_2708_);
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = lean_nat_dec_eq(v___x_2709_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v_lastNotFlattened_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2712_ = lean_box(0);
v_lastNotFlattened_2713_ = lean_array_get(v___x_2712_, v_ds_2708_, v___x_2710_);
v___x_2714_ = lean_unsigned_to_nat(1u);
v___x_2715_ = lean_nat_dec_eq(v___x_2709_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v_lastFlattened_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v_fst_2720_; lean_object* v_snd_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_inc(v_lastNotFlattened_2713_);
v_lastFlattened_2716_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_2713_);
v___x_2717_ = l_Array_toSubarray___redArg(v_ds_2708_, v___x_2714_, v___x_2709_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_lastFlattened_2716_);
lean_ctor_set(v___x_2718_, 1, v_lastNotFlattened_2713_);
v___x_2719_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(v_sep_2707_, v___x_2717_, v___x_2718_);
v_fst_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_fst_2720_);
v_snd_2721_ = lean_ctor_get(v___x_2719_, 1);
lean_inc(v_snd_2721_);
lean_dec_ref(v___x_2719_);
v___x_2722_ = lean_unsigned_to_nat(2u);
v___x_2723_ = lean_mk_empty_array_with_capacity(v___x_2722_);
v___x_2724_ = lean_array_push(v___x_2723_, v_fst_2720_);
v___x_2725_ = lean_array_push(v___x_2724_, v_snd_2721_);
v___x_2726_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2725_);
return v___x_2726_;
}
else
{
lean_dec_ref(v_ds_2708_);
lean_dec(v_sep_2707_);
return v_lastNotFlattened_2713_;
}
}
else
{
lean_object* v___x_2727_; 
lean_dec_ref(v_ds_2708_);
lean_dec(v_sep_2707_);
v___x_2727_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing(lean_object* v_00_u03c4_2728_, lean_object* v_sep_2729_, lean_object* v_ds_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_2729_, v_ds_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0(lean_object* v_00_u03c4_2732_, lean_object* v_sep_2733_, lean_object* v_inst_2734_, lean_object* v_R_2735_, lean_object* v_a_2736_, lean_object* v_b_2737_, lean_object* v_c_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(v_sep_2733_, v_a_2736_, v_b_2737_);
return v___x_2739_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___closed__0));
v___x_2741_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(lean_object* v_a_2742_, lean_object* v_b_2743_){
_start:
{
lean_object* v_array_2744_; lean_object* v_start_2745_; lean_object* v_stop_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2790_; 
v_array_2744_ = lean_ctor_get(v_a_2742_, 0);
v_start_2745_ = lean_ctor_get(v_a_2742_, 1);
v_stop_2746_ = lean_ctor_get(v_a_2742_, 2);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_a_2742_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2748_ = v_a_2742_;
v_isShared_2749_ = v_isSharedCheck_2790_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_stop_2746_);
lean_inc(v_start_2745_);
lean_inc(v_array_2744_);
lean_dec(v_a_2742_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2790_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_nat_dec_lt(v_start_2745_, v_stop_2746_);
if (v___x_2750_ == 0)
{
lean_del_object(v___x_2748_);
lean_dec(v_stop_2746_);
lean_dec(v_start_2745_);
lean_dec_ref(v_array_2744_);
return v_b_2743_;
}
else
{
lean_object* v_fst_2751_; lean_object* v_snd_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2789_; 
v_fst_2751_ = lean_ctor_get(v_b_2743_, 0);
v_snd_2752_ = lean_ctor_get(v_b_2743_, 1);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_b_2743_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2754_ = v_b_2743_;
v_isShared_2755_ = v_isSharedCheck_2789_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_snd_2752_);
lean_inc(v_fst_2751_);
lean_dec(v_b_2743_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2789_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = lean_nat_add(v_start_2745_, v___x_2756_);
lean_inc_ref(v_array_2744_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 1, v___x_2757_);
v___x_2759_ = v___x_2748_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_array_2744_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_stop_2746_);
v___x_2759_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2760_ = lean_array_fget(v_array_2744_, v_start_2745_);
lean_dec(v_start_2745_);
lean_dec_ref(v_array_2744_);
v___x_2761_ = lean_unsigned_to_nat(2u);
v___x_2762_ = lean_mk_empty_array_with_capacity(v___x_2761_);
lean_inc(v_fst_2751_);
lean_inc_ref(v___x_2762_);
v___x_2763_ = lean_array_push(v___x_2762_, v_fst_2751_);
v___x_2764_ = lean_array_push(v___x_2763_, v_snd_2752_);
v___x_2765_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2764_);
v___x_2766_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
lean_inc(v___x_2760_);
v___x_2767_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_2760_);
v___x_2768_ = lean_unsigned_to_nat(3u);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2768_);
lean_inc_ref(v___x_2769_);
v___x_2770_ = lean_array_push(v___x_2769_, v_fst_2751_);
v___x_2771_ = lean_array_push(v___x_2770_, v___x_2766_);
lean_inc(v___x_2767_);
v___x_2772_ = lean_array_push(v___x_2771_, v___x_2767_);
v___x_2773_ = l_Lean_Fmt_Doc_join___redArg(v___x_2772_);
v___x_2774_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2775_ = lean_array_push(v___x_2769_, v___x_2765_);
v___x_2776_ = lean_array_push(v___x_2775_, v___x_2774_);
lean_inc_ref(v___x_2776_);
v___x_2777_ = lean_array_push(v___x_2776_, v___x_2767_);
v___x_2778_ = l_Lean_Fmt_Doc_join___redArg(v___x_2777_);
v___x_2779_ = lean_array_push(v___x_2762_, v___x_2773_);
v___x_2780_ = lean_array_push(v___x_2779_, v___x_2778_);
v___x_2781_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2780_);
v___x_2782_ = lean_array_push(v___x_2776_, v___x_2760_);
v___x_2783_ = l_Lean_Fmt_Doc_join___redArg(v___x_2782_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 1, v___x_2783_);
lean_ctor_set(v___x_2754_, 0, v___x_2781_);
v___x_2785_ = v___x_2754_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
v_a_2742_ = v___x_2759_;
v_b_2743_ = v___x_2785_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object* v_ds_2791_){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2792_ = lean_array_get_size(v_ds_2791_);
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = lean_nat_dec_eq(v___x_2792_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v_lastNotFlattened_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2795_ = lean_box(0);
v_lastNotFlattened_2796_ = lean_array_get(v___x_2795_, v_ds_2791_, v___x_2793_);
v___x_2797_ = lean_unsigned_to_nat(1u);
v___x_2798_ = lean_nat_dec_eq(v___x_2792_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v_lastFlattened_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v_fst_2803_; lean_object* v_snd_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_inc(v_lastNotFlattened_2796_);
v_lastFlattened_2799_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_2796_);
v___x_2800_ = l_Array_toSubarray___redArg(v_ds_2791_, v___x_2797_, v___x_2792_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v_lastFlattened_2799_);
lean_ctor_set(v___x_2801_, 1, v_lastNotFlattened_2796_);
v___x_2802_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(v___x_2800_, v___x_2801_);
v_fst_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_fst_2803_);
v_snd_2804_ = lean_ctor_get(v___x_2802_, 1);
lean_inc(v_snd_2804_);
lean_dec_ref(v___x_2802_);
v___x_2805_ = lean_unsigned_to_nat(2u);
v___x_2806_ = lean_mk_empty_array_with_capacity(v___x_2805_);
v___x_2807_ = lean_array_push(v___x_2806_, v_fst_2803_);
v___x_2808_ = lean_array_push(v___x_2807_, v_snd_2804_);
v___x_2809_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2808_);
return v___x_2809_;
}
else
{
lean_dec_ref(v_ds_2791_);
return v_lastNotFlattened_2796_;
}
}
else
{
lean_object* v___x_2810_; 
lean_dec_ref(v_ds_2791_);
v___x_2810_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace(lean_object* v_00_u03c4_2811_, lean_object* v_ds_2812_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_ds_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0(lean_object* v_00_u03c4_2814_, lean_object* v_inst_2815_, lean_object* v_R_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_, lean_object* v_c_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(v_a_2817_, v_b_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(lean_object* v_boundarySep_2821_, lean_object* v_a_2822_, lean_object* v_b_2823_){
_start:
{
lean_object* v_array_2824_; lean_object* v_start_2825_; lean_object* v_stop_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2875_; 
v_array_2824_ = lean_ctor_get(v_a_2822_, 0);
v_start_2825_ = lean_ctor_get(v_a_2822_, 1);
v_stop_2826_ = lean_ctor_get(v_a_2822_, 2);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_a_2822_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2828_ = v_a_2822_;
v_isShared_2829_ = v_isSharedCheck_2875_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_stop_2826_);
lean_inc(v_start_2825_);
lean_inc(v_array_2824_);
lean_dec(v_a_2822_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2875_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
uint8_t v___x_2830_; 
v___x_2830_ = lean_nat_dec_lt(v_start_2825_, v_stop_2826_);
if (v___x_2830_ == 0)
{
lean_del_object(v___x_2828_);
lean_dec(v_stop_2826_);
lean_dec(v_start_2825_);
lean_dec_ref(v_array_2824_);
lean_dec(v_boundarySep_2821_);
return v_b_2823_;
}
else
{
lean_object* v___x_2831_; lean_object* v_fst_2832_; lean_object* v_snd_2833_; lean_object* v_fst_2834_; lean_object* v_snd_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2874_; 
v___x_2831_ = lean_array_fget_borrowed(v_array_2824_, v_start_2825_);
v_fst_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_fst_2832_);
v_snd_2833_ = lean_ctor_get(v___x_2831_, 1);
lean_inc(v_snd_2833_);
v_fst_2834_ = lean_ctor_get(v_b_2823_, 0);
v_snd_2835_ = lean_ctor_get(v_b_2823_, 1);
v_isSharedCheck_2874_ = !lean_is_exclusive(v_b_2823_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2837_ = v_b_2823_;
v_isShared_2838_ = v_isSharedCheck_2874_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snd_2835_);
lean_inc(v_fst_2834_);
lean_dec(v_b_2823_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2874_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2839_ = lean_unsigned_to_nat(1u);
v___x_2840_ = lean_nat_add(v_start_2825_, v___x_2839_);
lean_dec(v_start_2825_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 1, v___x_2840_);
v___x_2842_ = v___x_2828_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_array_2824_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___x_2840_);
lean_ctor_set(v_reuseFailAlloc_2873_, 2, v_stop_2826_);
v___x_2842_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___y_2849_; uint8_t v___x_2871_; 
v___x_2843_ = lean_unsigned_to_nat(2u);
v___x_2844_ = lean_mk_empty_array_with_capacity(v___x_2843_);
lean_inc(v_fst_2834_);
lean_inc_ref(v___x_2844_);
v___x_2845_ = lean_array_push(v___x_2844_, v_fst_2834_);
v___x_2846_ = lean_array_push(v___x_2845_, v_snd_2835_);
v___x_2847_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2846_);
v___x_2871_ = lean_unbox(v_snd_2833_);
lean_dec(v_snd_2833_);
if (v___x_2871_ == 0)
{
lean_object* v_sep_2872_; 
v_sep_2872_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
v___y_2849_ = v_sep_2872_;
goto v___jp_2848_;
}
else
{
lean_inc(v_boundarySep_2821_);
v___y_2849_ = v_boundarySep_2821_;
goto v___jp_2848_;
}
v___jp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_inc(v_fst_2832_);
v___x_2850_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_2832_);
v___x_2851_ = lean_unsigned_to_nat(3u);
v___x_2852_ = lean_mk_empty_array_with_capacity(v___x_2851_);
lean_inc_ref(v___x_2852_);
v___x_2853_ = lean_array_push(v___x_2852_, v_fst_2834_);
v___x_2854_ = lean_array_push(v___x_2853_, v___y_2849_);
lean_inc(v___x_2850_);
v___x_2855_ = lean_array_push(v___x_2854_, v___x_2850_);
v___x_2856_ = l_Lean_Fmt_Doc_join___redArg(v___x_2855_);
v___x_2857_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2858_ = lean_array_push(v___x_2852_, v___x_2847_);
v___x_2859_ = lean_array_push(v___x_2858_, v___x_2857_);
lean_inc_ref(v___x_2859_);
v___x_2860_ = lean_array_push(v___x_2859_, v___x_2850_);
v___x_2861_ = l_Lean_Fmt_Doc_join___redArg(v___x_2860_);
v___x_2862_ = lean_array_push(v___x_2844_, v___x_2856_);
v___x_2863_ = lean_array_push(v___x_2862_, v___x_2861_);
v___x_2864_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2863_);
v___x_2865_ = lean_array_push(v___x_2859_, v_fst_2832_);
v___x_2866_ = l_Lean_Fmt_Doc_join___redArg(v___x_2865_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v___x_2866_);
lean_ctor_set(v___x_2837_, 0, v___x_2864_);
v___x_2868_ = v___x_2837_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
v_a_2822_ = v___x_2842_;
v_b_2823_ = v___x_2868_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(size_t v_sz_2876_, size_t v_i_2877_, lean_object* v_bs_2878_){
_start:
{
uint8_t v___x_2879_; 
v___x_2879_ = lean_usize_dec_lt(v_i_2877_, v_sz_2876_);
if (v___x_2879_ == 0)
{
return v_bs_2878_;
}
else
{
lean_object* v_v_2880_; lean_object* v___x_2881_; lean_object* v_bs_x27_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; size_t v___x_2887_; size_t v___x_2888_; lean_object* v___x_2889_; 
v_v_2880_ = lean_array_uget(v_bs_2878_, v_i_2877_);
v___x_2881_ = lean_unsigned_to_nat(0u);
v_bs_x27_2882_ = lean_array_uset(v_bs_2878_, v_i_2877_, v___x_2881_);
v___x_2883_ = lean_usize_to_nat(v_i_2877_);
v___x_2884_ = lean_nat_dec_eq(v___x_2883_, v___x_2881_);
lean_dec(v___x_2883_);
v___x_2885_ = lean_box(v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v_v_2880_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = ((size_t)1ULL);
v___x_2888_ = lean_usize_add(v_i_2877_, v___x_2887_);
v___x_2889_ = lean_array_uset(v_bs_x27_2882_, v_i_2877_, v___x_2886_);
v_i_2877_ = v___x_2888_;
v_bs_2878_ = v___x_2889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg___boxed(lean_object* v_sz_2891_, lean_object* v_i_2892_, lean_object* v_bs_2893_){
_start:
{
size_t v_sz_boxed_2894_; size_t v_i_boxed_2895_; lean_object* v_res_2896_; 
v_sz_boxed_2894_ = lean_unbox_usize(v_sz_2891_);
lean_dec(v_sz_2891_);
v_i_boxed_2895_ = lean_unbox_usize(v_i_2892_);
lean_dec(v_i_2892_);
v_res_2896_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_boxed_2894_, v_i_boxed_2895_, v_bs_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(lean_object* v_as_2897_, size_t v_i_2898_, size_t v_stop_2899_, lean_object* v_b_2900_){
_start:
{
uint8_t v___x_2901_; 
v___x_2901_ = lean_usize_dec_eq(v_i_2898_, v_stop_2899_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; size_t v_sz_2903_; size_t v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; size_t v___x_2907_; size_t v___x_2908_; 
v___x_2902_ = lean_array_uget_borrowed(v_as_2897_, v_i_2898_);
v_sz_2903_ = lean_array_size(v___x_2902_);
v___x_2904_ = ((size_t)0ULL);
lean_inc(v___x_2902_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_2903_, v___x_2904_, v___x_2902_);
v___x_2906_ = l_Array_append___redArg(v_b_2900_, v___x_2905_);
lean_dec_ref(v___x_2905_);
v___x_2907_ = ((size_t)1ULL);
v___x_2908_ = lean_usize_add(v_i_2898_, v___x_2907_);
v_i_2898_ = v___x_2908_;
v_b_2900_ = v___x_2906_;
goto _start;
}
else
{
return v_b_2900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg___boxed(lean_object* v_as_2910_, lean_object* v_i_2911_, lean_object* v_stop_2912_, lean_object* v_b_2913_){
_start:
{
size_t v_i_boxed_2914_; size_t v_stop_boxed_2915_; lean_object* v_res_2916_; 
v_i_boxed_2914_ = lean_unbox_usize(v_i_2911_);
lean_dec(v_i_2911_);
v_stop_boxed_2915_ = lean_unbox_usize(v_stop_2912_);
lean_dec(v_stop_2912_);
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_2910_, v_i_boxed_2914_, v_stop_boxed_2915_, v_b_2913_);
lean_dec_ref(v_as_2910_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(lean_object* v_boundaryPenalty_2923_, lean_object* v_dss_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___y_2927_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v___x_2925_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__0));
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = ((lean_object*)(l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___closed__1));
v___x_2958_ = lean_array_get_size(v_dss_2924_);
v___x_2959_ = lean_nat_dec_lt(v___x_2956_, v___x_2958_);
if (v___x_2959_ == 0)
{
v___y_2927_ = v___x_2957_;
goto v___jp_2926_;
}
else
{
size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = ((size_t)0ULL);
v___x_2961_ = lean_usize_of_nat(v___x_2958_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_dss_2924_, v___x_2960_, v___x_2961_, v___x_2957_);
v___y_2927_ = v___x_2962_;
goto v___jp_2926_;
}
v___jp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2928_ = lean_array_get_size(v___y_2927_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v___x_2930_ = lean_nat_dec_eq(v___x_2928_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v_fst_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2953_; 
v___x_2931_ = lean_array_get(v___x_2925_, v___y_2927_, v___x_2929_);
v_fst_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2953_ == 0)
{
lean_object* v_unused_2954_; 
v_unused_2954_ = lean_ctor_get(v___x_2931_, 1);
lean_dec(v_unused_2954_);
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2953_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_fst_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2953_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = lean_unsigned_to_nat(1u);
v___x_2937_ = lean_nat_dec_eq(v___x_2928_, v___x_2936_);
if (v___x_2937_ == 0)
{
lean_object* v_sep_2938_; lean_object* v_boundarySep_2939_; lean_object* v_lastFlattened_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v_sep_2938_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
v_boundarySep_2939_ = l_Lean_Fmt_Doc_costing___override___redArg(v_boundaryPenalty_2923_, v_sep_2938_);
lean_inc(v_fst_2932_);
v_lastFlattened_2940_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_fst_2932_);
v___x_2941_ = l_Array_toSubarray___redArg(v___y_2927_, v___x_2936_, v___x_2928_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v_fst_2932_);
lean_ctor_set(v___x_2934_, 0, v_lastFlattened_2940_);
v___x_2943_ = v___x_2934_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_lastFlattened_2940_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_fst_2932_);
v___x_2943_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2944_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_boundarySep_2939_, v___x_2941_, v___x_2943_);
v_fst_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_fst_2945_);
v_snd_2946_ = lean_ctor_get(v___x_2944_, 1);
lean_inc(v_snd_2946_);
lean_dec_ref(v___x_2944_);
v___x_2947_ = lean_unsigned_to_nat(2u);
v___x_2948_ = lean_mk_empty_array_with_capacity(v___x_2947_);
v___x_2949_ = lean_array_push(v___x_2948_, v_fst_2945_);
v___x_2950_ = lean_array_push(v___x_2949_, v_snd_2946_);
v___x_2951_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2950_);
return v___x_2951_;
}
}
else
{
lean_del_object(v___x_2934_);
lean_dec_ref(v___y_2927_);
lean_dec(v_boundaryPenalty_2923_);
return v_fst_2932_;
}
}
}
else
{
lean_object* v___x_2955_; 
lean_dec_ref(v___y_2927_);
lean_dec(v_boundaryPenalty_2923_);
v___x_2955_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg___boxed(lean_object* v_boundaryPenalty_2963_, lean_object* v_dss_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_2963_, v_dss_2964_);
lean_dec_ref(v_dss_2964_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(lean_object* v_00_u03c4_2966_, lean_object* v_boundaryPenalty_2967_, lean_object* v_dss_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___redArg(v_boundaryPenalty_2967_, v_dss_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries___boxed(lean_object* v_00_u03c4_2970_, lean_object* v_boundaryPenalty_2971_, lean_object* v_dss_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries(v_00_u03c4_2970_, v_boundaryPenalty_2971_, v_dss_2972_);
lean_dec_ref(v_dss_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(lean_object* v_00_u03c4_2974_, lean_object* v_as_2975_, size_t v_sz_2976_, size_t v_i_2977_, lean_object* v_bs_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___redArg(v_sz_2976_, v_i_2977_, v_bs_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0___boxed(lean_object* v_00_u03c4_2980_, lean_object* v_as_2981_, lean_object* v_sz_2982_, lean_object* v_i_2983_, lean_object* v_bs_2984_){
_start:
{
size_t v_sz_boxed_2985_; size_t v_i_boxed_2986_; lean_object* v_res_2987_; 
v_sz_boxed_2985_ = lean_unbox_usize(v_sz_2982_);
lean_dec(v_sz_2982_);
v_i_boxed_2986_ = lean_unbox_usize(v_i_2983_);
lean_dec(v_i_2983_);
v_res_2987_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__0(v_00_u03c4_2980_, v_as_2981_, v_sz_boxed_2985_, v_i_boxed_2986_, v_bs_2984_);
lean_dec_ref(v_as_2981_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1(lean_object* v_00_u03c4_2988_, lean_object* v_boundarySep_2989_, lean_object* v_inst_2990_, lean_object* v_R_2991_, lean_object* v_a_2992_, lean_object* v_b_2993_, lean_object* v_c_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__1___redArg(v_boundarySep_2989_, v_a_2992_, v_b_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(lean_object* v_00_u03c4_2996_, lean_object* v_as_2997_, size_t v_i_2998_, size_t v_stop_2999_, lean_object* v_b_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___redArg(v_as_2997_, v_i_2998_, v_stop_2999_, v_b_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2___boxed(lean_object* v_00_u03c4_3002_, lean_object* v_as_3003_, lean_object* v_i_3004_, lean_object* v_stop_3005_, lean_object* v_b_3006_){
_start:
{
size_t v_i_boxed_3007_; size_t v_stop_boxed_3008_; lean_object* v_res_3009_; 
v_i_boxed_3007_ = lean_unbox_usize(v_i_3004_);
lean_dec(v_i_3004_);
v_stop_boxed_3008_ = lean_unbox_usize(v_stop_3005_);
lean_dec(v_stop_3005_);
v_res_3009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Fmt_Doc_fillUsingSpaceWithSoftBoundaries_spec__2(v_00_u03c4_3002_, v_as_3003_, v_i_boxed_3007_, v_stop_boxed_3008_, v_b_3006_);
lean_dec_ref(v_as_3003_);
return v_res_3009_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3010_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
v___x_3011_ = lean_unsigned_to_nat(2u);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_3011_);
v___x_3013_ = lean_array_push(v___x_3012_, v___x_3010_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(lean_object* v_wrap_3014_, lean_object* v_as_3015_, size_t v_sz_3016_, size_t v_i_3017_, lean_object* v_b_3018_){
_start:
{
uint8_t v___x_3019_; 
v___x_3019_ = lean_usize_dec_lt(v_i_3017_, v_sz_3016_);
if (v___x_3019_ == 0)
{
lean_dec_ref(v_wrap_3014_);
return v_b_3018_;
}
else
{
lean_object* v_fst_3020_; lean_object* v_snd_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3057_; 
v_fst_3020_ = lean_ctor_get(v_b_3018_, 0);
v_snd_3021_ = lean_ctor_get(v_b_3018_, 1);
v_isSharedCheck_3057_ = !lean_is_exclusive(v_b_3018_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3023_ = v_b_3018_;
v_isShared_3024_ = v_isSharedCheck_3057_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_snd_3021_);
lean_inc(v_fst_3020_);
lean_dec(v_b_3018_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3057_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v_a_3025_ = lean_array_uget_borrowed(v_as_3015_, v_i_3017_);
v___x_3026_ = lean_unsigned_to_nat(2u);
v___x_3027_ = lean_mk_empty_array_with_capacity(v___x_3026_);
lean_inc(v_fst_3020_);
lean_inc_ref_n(v___x_3027_, 3);
v___x_3028_ = lean_array_push(v___x_3027_, v_fst_3020_);
v___x_3029_ = lean_array_push(v___x_3028_, v_snd_3021_);
v___x_3030_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3029_);
v___x_3031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_3032_ = lean_array_push(v___x_3031_, v___x_3030_);
v___x_3033_ = l_Lean_Fmt_Doc_join___redArg(v___x_3032_);
lean_inc_ref_n(v_wrap_3014_, 2);
v___x_3034_ = lean_apply_1(v_wrap_3014_, v___x_3033_);
lean_inc_n(v_a_3025_, 2);
v___x_3035_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_a_3025_);
v___x_3036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_3037_ = lean_array_push(v___x_3036_, v_fst_3020_);
v___x_3038_ = l_Lean_Fmt_Doc_join___redArg(v___x_3037_);
v___x_3039_ = lean_apply_1(v_wrap_3014_, v___x_3038_);
v___x_3040_ = lean_array_push(v___x_3027_, v___x_3035_);
lean_inc_ref(v___x_3040_);
v___x_3041_ = lean_array_push(v___x_3040_, v___x_3039_);
v___x_3042_ = l_Lean_Fmt_Doc_join___redArg(v___x_3041_);
lean_inc(v___x_3034_);
v___x_3043_ = lean_array_push(v___x_3040_, v___x_3034_);
v___x_3044_ = l_Lean_Fmt_Doc_join___redArg(v___x_3043_);
v___x_3045_ = lean_array_push(v___x_3027_, v___x_3042_);
v___x_3046_ = lean_array_push(v___x_3045_, v___x_3044_);
v___x_3047_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3046_);
v___x_3048_ = lean_array_push(v___x_3027_, v_a_3025_);
v___x_3049_ = lean_array_push(v___x_3048_, v___x_3034_);
v___x_3050_ = l_Lean_Fmt_Doc_join___redArg(v___x_3049_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v___x_3050_);
lean_ctor_set(v___x_3023_, 0, v___x_3047_);
v___x_3052_ = v___x_3023_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
size_t v___x_3053_; size_t v___x_3054_; 
v___x_3053_ = ((size_t)1ULL);
v___x_3054_ = lean_usize_add(v_i_3017_, v___x_3053_);
v_i_3017_ = v___x_3054_;
v_b_3018_ = v___x_3052_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___boxed(lean_object* v_wrap_3058_, lean_object* v_as_3059_, lean_object* v_sz_3060_, lean_object* v_i_3061_, lean_object* v_b_3062_){
_start:
{
size_t v_sz_boxed_3063_; size_t v_i_boxed_3064_; lean_object* v_res_3065_; 
v_sz_boxed_3063_ = lean_unbox_usize(v_sz_3060_);
lean_dec(v_sz_3060_);
v_i_boxed_3064_ = lean_unbox_usize(v_i_3061_);
lean_dec(v_i_3061_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_3058_, v_as_3059_, v_sz_boxed_3063_, v_i_boxed_3064_, v_b_3062_);
lean_dec_ref(v_as_3059_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object* v_ds_3066_, lean_object* v_wrap_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___x_3068_ = lean_array_get_size(v_ds_3066_);
v___x_3069_ = lean_unsigned_to_nat(0u);
v___x_3070_ = lean_nat_dec_eq(v___x_3068_, v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_restNotFlattened_3074_; uint8_t v___x_3075_; 
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = lean_nat_sub(v___x_3068_, v___x_3072_);
v_restNotFlattened_3074_ = lean_array_get(v___x_3071_, v_ds_3066_, v___x_3073_);
lean_dec(v___x_3073_);
v___x_3075_ = lean_nat_dec_eq(v___x_3068_, v___x_3072_);
if (v___x_3075_ == 0)
{
lean_object* v_restFlattened_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; size_t v_sz_3080_; size_t v___x_3081_; lean_object* v___x_3082_; lean_object* v_fst_3083_; lean_object* v_snd_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_inc(v_restNotFlattened_3074_);
v_restFlattened_3076_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_3074_);
v___x_3077_ = lean_array_pop(v_ds_3066_);
v___x_3078_ = l_Array_reverse___redArg(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3079_, 0, v_restFlattened_3076_);
lean_ctor_set(v___x_3079_, 1, v_restNotFlattened_3074_);
v_sz_3080_ = lean_array_size(v___x_3078_);
v___x_3081_ = ((size_t)0ULL);
v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_3067_, v___x_3078_, v_sz_3080_, v___x_3081_, v___x_3079_);
lean_dec_ref(v___x_3078_);
v_fst_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_fst_3083_);
v_snd_3084_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_snd_3084_);
lean_dec_ref(v___x_3082_);
v___x_3085_ = lean_unsigned_to_nat(2u);
v___x_3086_ = lean_mk_empty_array_with_capacity(v___x_3085_);
v___x_3087_ = lean_array_push(v___x_3086_, v_fst_3083_);
v___x_3088_ = lean_array_push(v___x_3087_, v_snd_3084_);
v___x_3089_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3088_);
return v___x_3089_;
}
else
{
lean_dec_ref(v_wrap_3067_);
lean_dec_ref(v_ds_3066_);
return v_restNotFlattened_3074_;
}
}
else
{
lean_object* v___x_3090_; 
lean_dec_ref(v_wrap_3067_);
lean_dec_ref(v_ds_3066_);
v___x_3090_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_3090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping(lean_object* v_00_u03c4_3091_, lean_object* v_ds_3092_, lean_object* v_wrap_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_ds_3092_, v_wrap_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0(lean_object* v_00_u03c4_3095_, lean_object* v_wrap_3096_, lean_object* v_as_3097_, size_t v_sz_3098_, size_t v_i_3099_, lean_object* v_b_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_3096_, v_as_3097_, v_sz_3098_, v_i_3099_, v_b_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___boxed(lean_object* v_00_u03c4_3102_, lean_object* v_wrap_3103_, lean_object* v_as_3104_, lean_object* v_sz_3105_, lean_object* v_i_3106_, lean_object* v_b_3107_){
_start:
{
size_t v_sz_boxed_3108_; size_t v_i_boxed_3109_; lean_object* v_res_3110_; 
v_sz_boxed_3108_ = lean_unbox_usize(v_sz_3105_);
lean_dec(v_sz_3105_);
v_i_boxed_3109_ = lean_unbox_usize(v_i_3106_);
lean_dec(v_i_3106_);
v_res_3110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0(v_00_u03c4_3102_, v_wrap_3103_, v_as_3104_, v_sz_boxed_3108_, v_i_boxed_3109_, v_b_3107_);
lean_dec_ref(v_as_3104_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object* v_inst_3111_){
_start:
{
uint8_t v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = 0;
v___x_3113_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3113_, 0, v_inst_3111_);
lean_ctor_set_uint8(v___x_3113_, sizeof(void*)*1, v___x_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default(lean_object* v_00_u03b1_3114_, lean_object* v_inst_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable___redArg(lean_object* v_inst_3117_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3117_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable(lean_object* v_a_3119_, lean_object* v_inst_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(size_t v_sz_3122_, size_t v_i_3123_, lean_object* v_bs_3124_){
_start:
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_usize_dec_lt(v_i_3123_, v_sz_3122_);
if (v___x_3125_ == 0)
{
return v_bs_3124_;
}
else
{
lean_object* v_v_3126_; lean_object* v_v_3127_; lean_object* v___x_3128_; lean_object* v_bs_x27_3129_; size_t v___x_3130_; size_t v___x_3131_; lean_object* v___x_3132_; 
v_v_3126_ = lean_array_uget_borrowed(v_bs_3124_, v_i_3123_);
v_v_3127_ = lean_ctor_get(v_v_3126_, 0);
lean_inc(v_v_3127_);
v___x_3128_ = lean_unsigned_to_nat(0u);
v_bs_x27_3129_ = lean_array_uset(v_bs_3124_, v_i_3123_, v___x_3128_);
v___x_3130_ = ((size_t)1ULL);
v___x_3131_ = lean_usize_add(v_i_3123_, v___x_3130_);
v___x_3132_ = lean_array_uset(v_bs_x27_3129_, v_i_3123_, v_v_3127_);
v_i_3123_ = v___x_3131_;
v_bs_3124_ = v___x_3132_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg___boxed(lean_object* v_sz_3134_, lean_object* v_i_3135_, lean_object* v_bs_3136_){
_start:
{
size_t v_sz_boxed_3137_; size_t v_i_boxed_3138_; lean_object* v_res_3139_; 
v_sz_boxed_3137_ = lean_unbox_usize(v_sz_3134_);
lean_dec(v_sz_3134_);
v_i_boxed_3138_ = lean_unbox_usize(v_i_3135_);
lean_dec(v_i_3135_);
v_res_3139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_boxed_3137_, v_i_boxed_3138_, v_bs_3136_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(size_t v_sz_3140_, size_t v_i_3141_, lean_object* v_bs_3142_){
_start:
{
uint8_t v___x_3143_; 
v___x_3143_ = lean_usize_dec_lt(v_i_3141_, v_sz_3140_);
if (v___x_3143_ == 0)
{
return v_bs_3142_;
}
else
{
lean_object* v_v_3144_; lean_object* v___x_3145_; lean_object* v_bs_x27_3146_; size_t v_sz_3147_; size_t v___x_3148_; lean_object* v___x_3149_; size_t v___x_3150_; size_t v___x_3151_; lean_object* v___x_3152_; 
v_v_3144_ = lean_array_uget(v_bs_3142_, v_i_3141_);
v___x_3145_ = lean_unsigned_to_nat(0u);
v_bs_x27_3146_ = lean_array_uset(v_bs_3142_, v_i_3141_, v___x_3145_);
v_sz_3147_ = lean_array_size(v_v_3144_);
v___x_3148_ = ((size_t)0ULL);
v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3147_, v___x_3148_, v_v_3144_);
v___x_3150_ = ((size_t)1ULL);
v___x_3151_ = lean_usize_add(v_i_3141_, v___x_3150_);
v___x_3152_ = lean_array_uset(v_bs_x27_3146_, v_i_3141_, v___x_3149_);
v_i_3141_ = v___x_3151_;
v_bs_3142_ = v___x_3152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg___boxed(lean_object* v_sz_3154_, lean_object* v_i_3155_, lean_object* v_bs_3156_){
_start:
{
size_t v_sz_boxed_3157_; size_t v_i_boxed_3158_; lean_object* v_res_3159_; 
v_sz_boxed_3157_ = lean_unbox_usize(v_sz_3154_);
lean_dec(v_sz_3154_);
v_i_boxed_3158_ = lean_unbox_usize(v_i_3155_);
lean_dec(v_i_3155_);
v_res_3159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_boxed_3157_, v_i_boxed_3158_, v_bs_3156_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
if (lean_obj_tag(v_a_3160_) == 0)
{
lean_object* v___x_3162_; 
v___x_3162_ = l_List_reverse___redArg(v_a_3161_);
return v___x_3162_;
}
else
{
lean_object* v_head_3163_; lean_object* v_tail_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3173_; 
v_head_3163_ = lean_ctor_get(v_a_3160_, 0);
v_tail_3164_ = lean_ctor_get(v_a_3160_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3166_ = v_a_3160_;
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_tail_3164_);
lean_inc(v_head_3163_);
lean_dec(v_a_3160_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3173_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = lean_array_mk(v_head_3163_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 1, v_a_3161_);
lean_ctor_set(v___x_3166_, 0, v___x_3168_);
v___x_3170_ = v___x_3166_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_a_3161_);
v___x_3170_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
v_a_3160_ = v_tail_3164_;
v_a_3161_ = v___x_3170_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
if (lean_obj_tag(v_a_3174_) == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3178_, 0, v_a_3175_);
lean_ctor_set(v___x_3178_, 1, v_a_3176_);
v___x_3179_ = l_List_reverse___redArg(v___x_3178_);
v___x_3180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
lean_ctor_set(v___x_3180_, 1, v_a_3177_);
v___x_3181_ = l_List_reverse___redArg(v___x_3180_);
return v___x_3181_;
}
else
{
lean_object* v_head_3182_; lean_object* v_tail_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3199_; 
v_head_3182_ = lean_ctor_get(v_a_3174_, 0);
v_tail_3183_ = lean_ctor_get(v_a_3174_, 1);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_a_3174_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3185_ = v_a_3174_;
v_isShared_3186_ = v_isSharedCheck_3199_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_tail_3183_);
lean_inc(v_head_3182_);
lean_dec(v_a_3174_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3199_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
uint8_t v_allowFill_3195_; 
v_allowFill_3195_ = lean_ctor_get_uint8(v_a_3175_, sizeof(void*)*1);
if (v_allowFill_3195_ == 0)
{
goto v___jp_3187_;
}
else
{
uint8_t v_allowFill_3196_; 
v_allowFill_3196_ = lean_ctor_get_uint8(v_head_3182_, sizeof(void*)*1);
if (v_allowFill_3196_ == 0)
{
goto v___jp_3187_;
}
else
{
lean_object* v___x_3197_; 
lean_del_object(v___x_3185_);
v___x_3197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3197_, 0, v_a_3175_);
lean_ctor_set(v___x_3197_, 1, v_a_3176_);
v_a_3174_ = v_tail_3183_;
v_a_3175_ = v_head_3182_;
v_a_3176_ = v___x_3197_;
goto _start;
}
}
v___jp_3187_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = lean_box(0);
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 1, v_a_3176_);
lean_ctor_set(v___x_3185_, 0, v_a_3175_);
v___x_3190_ = v___x_3185_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3175_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_a_3176_);
v___x_3190_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = l_List_reverse___redArg(v___x_3190_);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v_a_3177_);
v_a_3174_ = v_tail_3183_;
v_a_3175_ = v_head_3182_;
v_a_3176_ = v___x_3188_;
v_a_3177_ = v___x_3192_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(lean_object* v_x_3200_){
_start:
{
if (lean_obj_tag(v_x_3200_) == 0)
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_box(0);
return v___x_3201_;
}
else
{
lean_object* v_head_3202_; lean_object* v_tail_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_head_3202_ = lean_ctor_get(v_x_3200_, 0);
lean_inc(v_head_3202_);
v_tail_3203_ = lean_ctor_get(v_x_3200_, 1);
lean_inc(v_tail_3203_);
lean_dec_ref_known(v_x_3200_, 2);
v___x_3204_ = lean_box(0);
v___x_3205_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_tail_3203_, v_head_3202_, v___x_3204_, v___x_3204_);
return v___x_3205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups___redArg(lean_object* v_ds_3206_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; size_t v_sz_3212_; size_t v___x_3213_; lean_object* v___x_3214_; 
v___x_3207_ = lean_array_to_list(v_ds_3206_);
v___x_3208_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v___x_3207_);
v___x_3209_ = lean_box(0);
v___x_3210_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v___x_3208_, v___x_3209_);
v___x_3211_ = lean_array_mk(v___x_3210_);
v_sz_3212_ = lean_array_size(v___x_3211_);
v___x_3213_ = ((size_t)0ULL);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_3212_, v___x_3213_, v___x_3211_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups(lean_object* v_00_u03c4_3215_, lean_object* v_ds_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(lean_object* v_00_u03c4_3218_, size_t v_sz_3219_, size_t v_i_3220_, lean_object* v_bs_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_3219_, v_i_3220_, v_bs_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___boxed(lean_object* v_00_u03c4_3223_, lean_object* v_sz_3224_, lean_object* v_i_3225_, lean_object* v_bs_3226_){
_start:
{
size_t v_sz_boxed_3227_; size_t v_i_boxed_3228_; lean_object* v_res_3229_; 
v_sz_boxed_3227_ = lean_unbox_usize(v_sz_3224_);
lean_dec(v_sz_3224_);
v_i_boxed_3228_ = lean_unbox_usize(v_i_3225_);
lean_dec(v_i_3225_);
v_res_3229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(v_00_u03c4_3223_, v_sz_boxed_3227_, v_i_boxed_3228_, v_bs_3226_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1(lean_object* v_00_u03c4_3230_, lean_object* v_x_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v_x_3231_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2(lean_object* v_00_u03c4_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v_a_3234_, v_a_3235_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(lean_object* v_00_u03c4_3237_, size_t v_sz_3238_, size_t v_i_3239_, lean_object* v_bs_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_3238_, v_i_3239_, v_bs_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___boxed(lean_object* v_00_u03c4_3242_, lean_object* v_sz_3243_, lean_object* v_i_3244_, lean_object* v_bs_3245_){
_start:
{
size_t v_sz_boxed_3246_; size_t v_i_boxed_3247_; lean_object* v_res_3248_; 
v_sz_boxed_3246_ = lean_unbox_usize(v_sz_3243_);
lean_dec(v_sz_3243_);
v_i_boxed_3247_ = lean_unbox_usize(v_i_3244_);
lean_dec(v_i_3244_);
v_res_3248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(v_00_u03c4_3242_, v_sz_boxed_3246_, v_i_boxed_3247_, v_bs_3245_);
return v_res_3248_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1(lean_object* v_00_u03c4_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v___x_3254_; 
v___x_3254_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(lean_object* v_sep_3255_, size_t v_sz_3256_, size_t v_i_3257_, lean_object* v_bs_3258_){
_start:
{
uint8_t v___x_3259_; 
v___x_3259_ = lean_usize_dec_lt(v_i_3257_, v_sz_3256_);
if (v___x_3259_ == 0)
{
lean_dec(v_sep_3255_);
return v_bs_3258_;
}
else
{
lean_object* v_v_3260_; lean_object* v___x_3261_; lean_object* v_bs_x27_3262_; lean_object* v___x_3263_; size_t v___x_3264_; size_t v___x_3265_; lean_object* v___x_3266_; 
v_v_3260_ = lean_array_uget(v_bs_3258_, v_i_3257_);
v___x_3261_ = lean_unsigned_to_nat(0u);
v_bs_x27_3262_ = lean_array_uset(v_bs_3258_, v_i_3257_, v___x_3261_);
lean_inc(v_sep_3255_);
v___x_3263_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_3255_, v_v_3260_);
v___x_3264_ = ((size_t)1ULL);
v___x_3265_ = lean_usize_add(v_i_3257_, v___x_3264_);
v___x_3266_ = lean_array_uset(v_bs_x27_3262_, v_i_3257_, v___x_3263_);
v_i_3257_ = v___x_3265_;
v_bs_3258_ = v___x_3266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg___boxed(lean_object* v_sep_3268_, lean_object* v_sz_3269_, lean_object* v_i_3270_, lean_object* v_bs_3271_){
_start:
{
size_t v_sz_boxed_3272_; size_t v_i_boxed_3273_; lean_object* v_res_3274_; 
v_sz_boxed_3272_ = lean_unbox_usize(v_sz_3269_);
lean_dec(v_sz_3269_);
v_i_boxed_3273_ = lean_unbox_usize(v_i_3270_);
lean_dec(v_i_3270_);
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_3268_, v_sz_boxed_3272_, v_i_boxed_3273_, v_bs_3271_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing___redArg(lean_object* v_sep_3275_, lean_object* v_ds_3276_){
_start:
{
lean_object* v_fillGroups_3277_; lean_object* v___x_3278_; size_t v_sz_3279_; size_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
v_fillGroups_3277_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3276_);
v___x_3278_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v_sz_3279_ = lean_array_size(v_fillGroups_3277_);
v___x_3280_ = ((size_t)0ULL);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_3275_, v_sz_3279_, v___x_3280_, v_fillGroups_3277_);
v___x_3282_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_3278_, v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing(lean_object* v_00_u03c4_3283_, lean_object* v_sep_3284_, lean_object* v_ds_3285_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_Fmt_Doc_fillSomeUsing___redArg(v_sep_3284_, v_ds_3285_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0(lean_object* v_00_u03c4_3287_, lean_object* v_sep_3288_, size_t v_sz_3289_, size_t v_i_3290_, lean_object* v_bs_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_3288_, v_sz_3289_, v_i_3290_, v_bs_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___boxed(lean_object* v_00_u03c4_3293_, lean_object* v_sep_3294_, lean_object* v_sz_3295_, lean_object* v_i_3296_, lean_object* v_bs_3297_){
_start:
{
size_t v_sz_boxed_3298_; size_t v_i_boxed_3299_; lean_object* v_res_3300_; 
v_sz_boxed_3298_ = lean_unbox_usize(v_sz_3295_);
lean_dec(v_sz_3295_);
v_i_boxed_3299_ = lean_unbox_usize(v_i_3296_);
lean_dec(v_i_3296_);
v_res_3300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0(v_00_u03c4_3293_, v_sep_3294_, v_sz_boxed_3298_, v_i_boxed_3299_, v_bs_3297_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(size_t v_sz_3301_, size_t v_i_3302_, lean_object* v_bs_3303_){
_start:
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_usize_dec_lt(v_i_3302_, v_sz_3301_);
if (v___x_3304_ == 0)
{
return v_bs_3303_;
}
else
{
lean_object* v_v_3305_; lean_object* v___x_3306_; lean_object* v_bs_x27_3307_; lean_object* v___x_3308_; size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; 
v_v_3305_ = lean_array_uget(v_bs_3303_, v_i_3302_);
v___x_3306_ = lean_unsigned_to_nat(0u);
v_bs_x27_3307_ = lean_array_uset(v_bs_3303_, v_i_3302_, v___x_3306_);
v___x_3308_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_v_3305_);
v___x_3309_ = ((size_t)1ULL);
v___x_3310_ = lean_usize_add(v_i_3302_, v___x_3309_);
v___x_3311_ = lean_array_uset(v_bs_x27_3307_, v_i_3302_, v___x_3308_);
v_i_3302_ = v___x_3310_;
v_bs_3303_ = v___x_3311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg___boxed(lean_object* v_sz_3313_, lean_object* v_i_3314_, lean_object* v_bs_3315_){
_start:
{
size_t v_sz_boxed_3316_; size_t v_i_boxed_3317_; lean_object* v_res_3318_; 
v_sz_boxed_3316_ = lean_unbox_usize(v_sz_3313_);
lean_dec(v_sz_3313_);
v_i_boxed_3317_ = lean_unbox_usize(v_i_3314_);
lean_dec(v_i_3314_);
v_res_3318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_boxed_3316_, v_i_boxed_3317_, v_bs_3315_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object* v_ds_3319_){
_start:
{
lean_object* v_fillGroups_3320_; lean_object* v___x_3321_; size_t v_sz_3322_; size_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_fillGroups_3320_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_3319_);
v___x_3321_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v_sz_3322_ = lean_array_size(v_fillGroups_3320_);
v___x_3323_ = ((size_t)0ULL);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_3322_, v___x_3323_, v_fillGroups_3320_);
v___x_3325_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_3321_, v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace(lean_object* v_00_u03c4_3326_, lean_object* v_ds_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v_ds_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(lean_object* v_00_u03c4_3329_, size_t v_sz_3330_, size_t v_i_3331_, lean_object* v_bs_3332_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_3330_, v_i_3331_, v_bs_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___boxed(lean_object* v_00_u03c4_3334_, lean_object* v_sz_3335_, lean_object* v_i_3336_, lean_object* v_bs_3337_){
_start:
{
size_t v_sz_boxed_3338_; size_t v_i_boxed_3339_; lean_object* v_res_3340_; 
v_sz_boxed_3338_ = lean_unbox_usize(v_sz_3335_);
lean_dec(v_sz_3335_);
v_i_boxed_3339_ = lean_unbox_usize(v_i_3336_);
lean_dec(v_i_3336_);
v_res_3340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(v_00_u03c4_3334_, v_sz_boxed_3338_, v_i_boxed_3339_, v_bs_3337_);
return v_res_3340_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3341_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_3342_ = lean_unsigned_to_nat(2u);
v___x_3343_ = lean_mk_empty_array_with_capacity(v___x_3342_);
v___x_3344_ = lean_array_push(v___x_3343_, v___x_3341_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(lean_object* v_wrap_3345_, lean_object* v_as_3346_, size_t v_sz_3347_, size_t v_i_3348_, lean_object* v_b_3349_){
_start:
{
uint8_t v___x_3350_; 
v___x_3350_ = lean_usize_dec_lt(v_i_3348_, v_sz_3347_);
if (v___x_3350_ == 0)
{
lean_dec_ref(v_wrap_3345_);
return v_b_3349_;
}
else
{
lean_object* v_snd_3351_; lean_object* v_fst_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3418_; 
v_snd_3351_ = lean_ctor_get(v_b_3349_, 1);
v_fst_3352_ = lean_ctor_get(v_b_3349_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_b_3349_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3354_ = v_b_3349_;
v_isShared_3355_ = v_isSharedCheck_3418_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_snd_3351_);
lean_inc(v_fst_3352_);
lean_dec(v_b_3349_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3418_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3417_; 
v_fst_3356_ = lean_ctor_get(v_snd_3351_, 0);
v_snd_3357_ = lean_ctor_get(v_snd_3351_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_snd_3351_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3359_ = v_snd_3351_;
v_isShared_3360_ = v_isSharedCheck_3417_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_snd_3357_);
lean_inc(v_fst_3356_);
lean_dec(v_snd_3351_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3417_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_a_3361_; lean_object* v_restFlattened_3363_; lean_object* v_restNotFlattened_3364_; lean_object* v_v_3376_; uint8_t v_allowFill_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3361_ = lean_array_uget_borrowed(v_as_3346_, v_i_3348_);
v_v_3376_ = lean_ctor_get(v_a_3361_, 0);
v_allowFill_3377_ = lean_ctor_get_uint8(v_a_3361_, sizeof(void*)*1);
v___x_3378_ = lean_unsigned_to_nat(2u);
v___x_3379_ = lean_mk_empty_array_with_capacity(v___x_3378_);
lean_inc(v_fst_3352_);
lean_inc_ref(v___x_3379_);
v___x_3380_ = lean_array_push(v___x_3379_, v_fst_3352_);
v___x_3381_ = lean_array_push(v___x_3380_, v_fst_3356_);
v___x_3382_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3381_);
if (v_allowFill_3377_ == 0)
{
lean_dec(v_snd_3357_);
lean_dec(v_fst_3352_);
goto v___jp_3383_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_unbox(v_snd_3357_);
lean_dec(v_snd_3357_);
if (v___x_3396_ == 0)
{
lean_dec(v_fst_3352_);
goto v___jp_3383_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3397_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_3398_ = lean_array_push(v___x_3397_, v___x_3382_);
v___x_3399_ = l_Lean_Fmt_Doc_join___redArg(v___x_3398_);
lean_inc_ref_n(v_wrap_3345_, 2);
v___x_3400_ = lean_apply_1(v_wrap_3345_, v___x_3399_);
lean_inc_n(v_v_3376_, 2);
v___x_3401_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_3376_);
v___x_3402_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_3403_ = lean_array_push(v___x_3402_, v_fst_3352_);
v___x_3404_ = l_Lean_Fmt_Doc_join___redArg(v___x_3403_);
v___x_3405_ = lean_apply_1(v_wrap_3345_, v___x_3404_);
lean_inc_ref_n(v___x_3379_, 2);
v___x_3406_ = lean_array_push(v___x_3379_, v___x_3401_);
lean_inc_ref(v___x_3406_);
v___x_3407_ = lean_array_push(v___x_3406_, v___x_3405_);
v___x_3408_ = l_Lean_Fmt_Doc_join___redArg(v___x_3407_);
lean_inc(v___x_3400_);
v___x_3409_ = lean_array_push(v___x_3406_, v___x_3400_);
v___x_3410_ = l_Lean_Fmt_Doc_join___redArg(v___x_3409_);
v___x_3411_ = lean_array_push(v___x_3379_, v___x_3408_);
v___x_3412_ = lean_array_push(v___x_3411_, v___x_3410_);
v___x_3413_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3412_);
v___x_3414_ = lean_array_push(v___x_3379_, v_v_3376_);
v___x_3415_ = lean_array_push(v___x_3414_, v___x_3400_);
v___x_3416_ = l_Lean_Fmt_Doc_join___redArg(v___x_3415_);
v_restFlattened_3363_ = v___x_3413_;
v_restNotFlattened_3364_ = v___x_3416_;
goto v___jp_3362_;
}
}
v___jp_3362_:
{
uint8_t v_allowFill_3365_; lean_object* v___x_3366_; lean_object* v___x_3368_; 
v_allowFill_3365_ = lean_ctor_get_uint8(v_a_3361_, sizeof(void*)*1);
v___x_3366_ = lean_box(v_allowFill_3365_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3366_);
lean_ctor_set(v___x_3359_, 0, v_restNotFlattened_3364_);
v___x_3368_ = v___x_3359_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_restNotFlattened_3364_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3366_);
v___x_3368_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3370_; 
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 1, v___x_3368_);
lean_ctor_set(v___x_3354_, 0, v_restFlattened_3363_);
v___x_3370_ = v___x_3354_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_restFlattened_3363_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
size_t v___x_3371_; size_t v___x_3372_; 
v___x_3371_ = ((size_t)1ULL);
v___x_3372_ = lean_usize_add(v_i_3348_, v___x_3371_);
v_i_3348_ = v___x_3372_;
v_b_3349_ = v___x_3370_;
goto _start;
}
}
}
v___jp_3383_:
{
lean_object* v_v_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_v_3384_ = lean_ctor_get(v_a_3361_, 0);
v___x_3385_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_3386_ = lean_array_push(v___x_3385_, v___x_3382_);
v___x_3387_ = l_Lean_Fmt_Doc_join___redArg(v___x_3386_);
lean_inc_ref(v_wrap_3345_);
v___x_3388_ = lean_apply_1(v_wrap_3345_, v___x_3387_);
lean_inc_n(v_v_3384_, 2);
v___x_3389_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_3384_);
lean_inc_ref(v___x_3379_);
v___x_3390_ = lean_array_push(v___x_3379_, v___x_3389_);
lean_inc(v___x_3388_);
v___x_3391_ = lean_array_push(v___x_3390_, v___x_3388_);
v___x_3392_ = l_Lean_Fmt_Doc_join___redArg(v___x_3391_);
v___x_3393_ = lean_array_push(v___x_3379_, v_v_3384_);
v___x_3394_ = lean_array_push(v___x_3393_, v___x_3388_);
v___x_3395_ = l_Lean_Fmt_Doc_join___redArg(v___x_3394_);
v_restFlattened_3363_ = v___x_3392_;
v_restNotFlattened_3364_ = v___x_3395_;
goto v___jp_3362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___boxed(lean_object* v_wrap_3419_, lean_object* v_as_3420_, lean_object* v_sz_3421_, lean_object* v_i_3422_, lean_object* v_b_3423_){
_start:
{
size_t v_sz_boxed_3424_; size_t v_i_boxed_3425_; lean_object* v_res_3426_; 
v_sz_boxed_3424_ = lean_unbox_usize(v_sz_3421_);
lean_dec(v_sz_3421_);
v_i_boxed_3425_ = lean_unbox_usize(v_i_3422_);
lean_dec(v_i_3422_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_3419_, v_as_3420_, v_sz_boxed_3424_, v_i_boxed_3425_, v_b_3423_);
lean_dec_ref(v_as_3420_);
return v_res_3426_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_box(0);
v___x_3428_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_3427_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object* v_ds_3429_, lean_object* v_wrap_3430_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3431_ = lean_array_get_size(v_ds_3429_);
v___x_3432_ = lean_unsigned_to_nat(0u);
v___x_3433_ = lean_nat_dec_eq(v___x_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_last_3437_; uint8_t v___x_3438_; 
v___x_3434_ = lean_obj_once(&l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0, &l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0);
v___x_3435_ = lean_unsigned_to_nat(1u);
v___x_3436_ = lean_nat_sub(v___x_3431_, v___x_3435_);
v_last_3437_ = lean_array_get_borrowed(v___x_3434_, v_ds_3429_, v___x_3436_);
lean_dec(v___x_3436_);
v___x_3438_ = lean_nat_dec_eq(v___x_3431_, v___x_3435_);
if (v___x_3438_ == 0)
{
lean_object* v_v_3439_; uint8_t v_allowFill_3440_; lean_object* v_restFlattened_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; size_t v_sz_3447_; size_t v___x_3448_; lean_object* v___x_3449_; lean_object* v_snd_3450_; lean_object* v_fst_3451_; lean_object* v_fst_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_v_3439_ = lean_ctor_get(v_last_3437_, 0);
lean_inc_n(v_v_3439_, 2);
v_allowFill_3440_ = lean_ctor_get_uint8(v_last_3437_, sizeof(void*)*1);
v_restFlattened_3441_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_3439_);
v___x_3442_ = lean_array_pop(v_ds_3429_);
v___x_3443_ = l_Array_reverse___redArg(v___x_3442_);
v___x_3444_ = lean_box(v_allowFill_3440_);
v___x_3445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3445_, 0, v_v_3439_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_restFlattened_3441_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v_sz_3447_ = lean_array_size(v___x_3443_);
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_3430_, v___x_3443_, v_sz_3447_, v___x_3448_, v___x_3446_);
lean_dec_ref(v___x_3443_);
v_snd_3450_ = lean_ctor_get(v___x_3449_, 1);
lean_inc(v_snd_3450_);
v_fst_3451_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_fst_3451_);
lean_dec_ref(v___x_3449_);
v_fst_3452_ = lean_ctor_get(v_snd_3450_, 0);
lean_inc(v_fst_3452_);
lean_dec(v_snd_3450_);
v___x_3453_ = lean_unsigned_to_nat(2u);
v___x_3454_ = lean_mk_empty_array_with_capacity(v___x_3453_);
v___x_3455_ = lean_array_push(v___x_3454_, v_fst_3451_);
v___x_3456_ = lean_array_push(v___x_3455_, v_fst_3452_);
v___x_3457_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3456_);
return v___x_3457_;
}
else
{
lean_object* v_v_3458_; 
lean_inc(v_last_3437_);
lean_dec_ref(v_wrap_3430_);
lean_dec_ref(v_ds_3429_);
v_v_3458_ = lean_ctor_get(v_last_3437_, 0);
lean_inc(v_v_3458_);
lean_dec(v_last_3437_);
return v_v_3458_;
}
}
else
{
lean_object* v___x_3459_; 
lean_dec_ref(v_wrap_3430_);
lean_dec_ref(v_ds_3429_);
v___x_3459_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_3459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping(lean_object* v_00_u03c4_3460_, lean_object* v_ds_3461_, lean_object* v_wrap_3462_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_3461_, v_wrap_3462_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0(lean_object* v_00_u03c4_3464_, lean_object* v_wrap_3465_, lean_object* v_as_3466_, size_t v_sz_3467_, size_t v_i_3468_, lean_object* v_b_3469_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_3465_, v_as_3466_, v_sz_3467_, v_i_3468_, v_b_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___boxed(lean_object* v_00_u03c4_3471_, lean_object* v_wrap_3472_, lean_object* v_as_3473_, lean_object* v_sz_3474_, lean_object* v_i_3475_, lean_object* v_b_3476_){
_start:
{
size_t v_sz_boxed_3477_; size_t v_i_boxed_3478_; lean_object* v_res_3479_; 
v_sz_boxed_3477_ = lean_unbox_usize(v_sz_3474_);
lean_dec(v_sz_3474_);
v_i_boxed_3478_ = lean_unbox_usize(v_i_3475_);
lean_dec(v_i_3475_);
v_res_3479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0(v_00_u03c4_3471_, v_wrap_3472_, v_as_3473_, v_sz_boxed_3477_, v_i_boxed_3478_, v_b_3476_);
lean_dec_ref(v_as_3473_);
return v_res_3479_;
}
}
static size_t _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_3480_; size_t v___x_3481_; 
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = lean_usize_of_nat(v___x_3480_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default___redArg(lean_object* v_inst_3482_){
_start:
{
size_t v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_usize_once(&l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0);
v___x_3484_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_3484_, 0, v_inst_3482_);
lean_ctor_set_usize(v___x_3484_, 1, v___x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default(lean_object* v_00_u03b1_3485_, lean_object* v_inst_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey___redArg(lean_object* v_inst_3488_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey(lean_object* v_a_3490_, lean_object* v_inst_3491_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object* v_v_3493_){
_start:
{
size_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = lean_ptr_addr(v_v_3493_);
v___x_3495_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_3495_, 0, v_v_3493_);
lean_ctor_set_usize(v___x_3495_, 1, v___x_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey(lean_object* v_00_u03b1_3496_, lean_object* v_v_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___lam__0(lean_object* v_v1_3499_, lean_object* v_v2_3500_){
_start:
{
size_t v_ptr_3501_; size_t v_ptr_3502_; uint8_t v___x_3503_; 
v_ptr_3501_ = lean_ctor_get_usize(v_v1_3499_, 1);
v_ptr_3502_ = lean_ctor_get_usize(v_v2_3500_, 1);
v___x_3503_ = lean_usize_dec_eq(v_ptr_3501_, v_ptr_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___lam__0___boxed(lean_object* v_v1_3504_, lean_object* v_v2_3505_){
_start:
{
uint8_t v_res_3506_; lean_object* v_r_3507_; 
v_res_3506_ = l_Lean_Fmt_instBEqPtrKey___lam__0(v_v1_3504_, v_v2_3505_);
lean_dec_ref(v_v2_3505_);
lean_dec_ref(v_v1_3504_);
v_r_3507_ = lean_box(v_res_3506_);
return v_r_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object* v_00_u03b1_3509_){
_start:
{
lean_object* v___f_3510_; 
v___f_3510_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___closed__0));
return v___f_3510_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___lam__0(lean_object* v_v_3511_){
_start:
{
size_t v_ptr_3512_; uint64_t v___x_3513_; 
v_ptr_3512_ = lean_ctor_get_usize(v_v_3511_, 1);
v___x_3513_ = lean_usize_to_uint64(v_ptr_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___lam__0___boxed(lean_object* v_v_3514_){
_start:
{
uint64_t v_res_3515_; lean_object* v_r_3516_; 
v_res_3515_ = l_Lean_Fmt_instHashablePtrKey___lam__0(v_v_3514_);
lean_dec_ref(v_v_3514_);
v_r_3516_ = lean_box_uint64(v_res_3515_);
return v_r_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey(lean_object* v_00_u03b1_3518_){
_start:
{
lean_object* v___f_3519_; 
v___f_3519_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___closed__0));
return v___f_3519_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(lean_object* v_x_3520_, lean_object* v_x_3521_){
_start:
{
lean_object* v_aPtr_3522_; lean_object* v_aPtr_3523_; lean_object* v_bPtr_3524_; lean_object* v_bPtr_3525_; size_t v_ptr_3526_; size_t v_ptr_3527_; uint8_t v___x_3528_; 
v_aPtr_3522_ = lean_ctor_get(v_x_3520_, 0);
v_aPtr_3523_ = lean_ctor_get(v_x_3521_, 0);
v_bPtr_3524_ = lean_ctor_get(v_x_3520_, 1);
v_bPtr_3525_ = lean_ctor_get(v_x_3521_, 1);
v_ptr_3526_ = lean_ctor_get_usize(v_aPtr_3522_, 1);
v_ptr_3527_ = lean_ctor_get_usize(v_aPtr_3523_, 1);
v___x_3528_ = lean_usize_dec_eq(v_ptr_3526_, v_ptr_3527_);
if (v___x_3528_ == 0)
{
return v___x_3528_;
}
else
{
size_t v_ptr_3529_; size_t v_ptr_3530_; uint8_t v___x_3531_; 
v_ptr_3529_ = lean_ctor_get_usize(v_bPtr_3524_, 1);
v_ptr_3530_ = lean_ctor_get_usize(v_bPtr_3525_, 1);
v___x_3531_ = lean_usize_dec_eq(v_ptr_3529_, v_ptr_3530_);
return v___x_3531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg___boxed(lean_object* v_x_3532_, lean_object* v_x_3533_){
_start:
{
uint8_t v_res_3534_; lean_object* v_r_3535_; 
v_res_3534_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_3532_, v_x_3533_);
lean_dec_ref(v_x_3533_);
lean_dec_ref(v_x_3532_);
v_r_3535_ = lean_box(v_res_3534_);
return v_r_3535_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq(lean_object* v_00_u03c4_3536_, lean_object* v_inst_3537_, lean_object* v_x_3538_, lean_object* v_x_3539_){
_start:
{
uint8_t v___x_3540_; 
v___x_3540_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_3538_, v_x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed(lean_object* v_00_u03c4_3541_, lean_object* v_inst_3542_, lean_object* v_x_3543_, lean_object* v_x_3544_){
_start:
{
uint8_t v_res_3545_; lean_object* v_r_3546_; 
v_res_3545_ = l_Lean_Fmt_instBEqBEqCacheKey_beq(v_00_u03c4_3541_, v_inst_3542_, v_x_3543_, v_x_3544_);
lean_dec_ref(v_x_3544_);
lean_dec_ref(v_x_3543_);
lean_dec_ref(v_inst_3542_);
v_r_3546_ = lean_box(v_res_3545_);
return v_r_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey___redArg(lean_object* v_inst_3547_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_3548_, 0, lean_box(0));
lean_closure_set(v___x_3548_, 1, v_inst_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey(lean_object* v_00_u03c4_3549_, lean_object* v_inst_3550_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_3551_, 0, lean_box(0));
lean_closure_set(v___x_3551_, 1, v_inst_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(lean_object* v_x_3552_){
_start:
{
lean_object* v_aPtr_3553_; lean_object* v_bPtr_3554_; size_t v_ptr_3555_; size_t v_ptr_3556_; uint64_t v___x_3557_; uint64_t v___x_3558_; uint64_t v___x_3559_; uint64_t v___x_3560_; uint64_t v___x_3561_; 
v_aPtr_3553_ = lean_ctor_get(v_x_3552_, 0);
v_bPtr_3554_ = lean_ctor_get(v_x_3552_, 1);
v_ptr_3555_ = lean_ctor_get_usize(v_aPtr_3553_, 1);
v_ptr_3556_ = lean_ctor_get_usize(v_bPtr_3554_, 1);
v___x_3557_ = 0ULL;
v___x_3558_ = lean_usize_to_uint64(v_ptr_3555_);
v___x_3559_ = lean_uint64_mix_hash(v___x_3557_, v___x_3558_);
v___x_3560_ = lean_usize_to_uint64(v_ptr_3556_);
v___x_3561_ = lean_uint64_mix_hash(v___x_3559_, v___x_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg___boxed(lean_object* v_x_3562_){
_start:
{
uint64_t v_res_3563_; lean_object* v_r_3564_; 
v_res_3563_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_3562_);
lean_dec_ref(v_x_3562_);
v_r_3564_ = lean_box_uint64(v_res_3563_);
return v_r_3564_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash(lean_object* v_00_u03c4_3565_, lean_object* v_inst_3566_, lean_object* v_x_3567_){
_start:
{
uint64_t v___x_3568_; 
v___x_3568_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_3567_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed(lean_object* v_00_u03c4_3569_, lean_object* v_inst_3570_, lean_object* v_x_3571_){
_start:
{
uint64_t v_res_3572_; lean_object* v_r_3573_; 
v_res_3572_ = l_Lean_Fmt_instHashableBEqCacheKey_hash(v_00_u03c4_3569_, v_inst_3570_, v_x_3571_);
lean_dec_ref(v_x_3571_);
lean_dec_ref(v_inst_3570_);
v_r_3573_ = lean_box_uint64(v_res_3572_);
return v_r_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey___redArg(lean_object* v_inst_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_3575_, 0, lean_box(0));
lean_closure_set(v___x_3575_, 1, v_inst_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey(lean_object* v_00_u03c4_3576_, lean_object* v_inst_3577_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_3578_, 0, lean_box(0));
lean_closure_set(v___x_3578_, 1, v_inst_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1___redArg(lean_object* v_a_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1(lean_object* v_00_u03c4_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4___redArg(lean_object* v_b_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4(lean_object* v_00_u03c4_3586_, lean_object* v_b_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_a_3591_, lean_object* v_b_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v___y_3599_; lean_object* v_da1_3604_; lean_object* v_da2_3605_; lean_object* v_db1_3606_; lean_object* v_db2_3607_; lean_object* v___y_3608_; lean_object* v_sa_3615_; lean_object* v_sb_3616_; lean_object* v___y_3617_; 
switch(lean_obj_tag(v_a_3591_))
{
case 0:
{
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
if (lean_obj_tag(v_b_3592_) == 0)
{
uint8_t v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = 1;
v___x_3622_ = lean_box(v___x_3621_);
v___x_3623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
lean_ctor_set(v___x_3623_, 1, v_a_3593_);
return v___x_3623_;
}
else
{
lean_dec(v_b_3592_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 1:
{
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
if (lean_obj_tag(v_b_3592_) == 1)
{
lean_object* v_f_3624_; lean_object* v_f_3625_; 
v_f_3624_ = lean_ctor_get(v_a_3591_, 2);
lean_inc_ref(v_f_3624_);
lean_dec_ref_known(v_a_3591_, 3);
v_f_3625_ = lean_ctor_get(v_b_3592_, 2);
lean_inc_ref(v_f_3625_);
lean_dec_ref_known(v_b_3592_, 3);
v_sa_3615_ = v_f_3624_;
v_sb_3616_ = v_f_3625_;
v___y_3617_ = v_a_3593_;
goto v___jp_3614_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 2:
{
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
if (lean_obj_tag(v_b_3592_) == 2)
{
lean_object* v_s_3626_; lean_object* v_s_3627_; 
v_s_3626_ = lean_ctor_get(v_a_3591_, 2);
lean_inc_ref(v_s_3626_);
lean_dec_ref_known(v_a_3591_, 3);
v_s_3627_ = lean_ctor_get(v_b_3592_, 2);
lean_inc_ref(v_s_3627_);
lean_dec_ref_known(v_b_3592_, 3);
v_sa_3615_ = v_s_3626_;
v_sb_3616_ = v_s_3627_;
v___y_3617_ = v_a_3593_;
goto v___jp_3614_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 3:
{
if (lean_obj_tag(v_b_3592_) == 3)
{
lean_object* v_id_3628_; lean_object* v_d_3629_; lean_object* v_id_3630_; lean_object* v_d_3631_; uint8_t v___x_3632_; 
v_id_3628_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_id_3628_);
v_d_3629_ = lean_ctor_get(v_a_3591_, 3);
lean_inc(v_d_3629_);
lean_dec_ref_known(v_a_3591_, 4);
v_id_3630_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_id_3630_);
v_d_3631_ = lean_ctor_get(v_b_3592_, 3);
lean_inc(v_d_3631_);
lean_dec_ref_known(v_b_3592_, 4);
v___x_3632_ = lean_nat_dec_eq(v_id_3628_, v_id_3630_);
lean_dec(v_id_3630_);
lean_dec(v_id_3628_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
lean_dec(v_d_3631_);
lean_dec(v_d_3629_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___x_3633_ = lean_box(v___x_3632_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v_a_3593_);
return v___x_3634_;
}
else
{
lean_object* v___x_3635_; 
v___x_3635_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3629_, v_d_3631_, v_a_3593_);
return v___x_3635_;
}
}
else
{
lean_dec_ref_known(v_a_3591_, 4);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 4:
{
if (lean_obj_tag(v_b_3592_) == 4)
{
lean_object* v_d_3636_; lean_object* v_d_3637_; lean_object* v___x_3638_; 
v_d_3636_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3636_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3637_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3637_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3638_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3636_, v_d_3637_, v_a_3593_);
return v___x_3638_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 5:
{
if (lean_obj_tag(v_b_3592_) == 5)
{
lean_object* v_d_3639_; lean_object* v_d_3640_; lean_object* v___x_3641_; 
v_d_3639_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3639_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3640_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3640_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3641_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3639_, v_d_3640_, v_a_3593_);
return v___x_3641_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 6:
{
if (lean_obj_tag(v_b_3592_) == 6)
{
lean_object* v_n_3642_; uint8_t v_isCumulative_3643_; lean_object* v_d_3644_; lean_object* v_n_3645_; uint8_t v_isCumulative_3646_; lean_object* v_d_3647_; uint8_t v___y_3649_; uint8_t v___x_3651_; 
v_n_3642_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_n_3642_);
v_isCumulative_3643_ = lean_ctor_get_uint8(v_a_3591_, sizeof(void*)*4 + 3);
v_d_3644_ = lean_ctor_get(v_a_3591_, 3);
lean_inc(v_d_3644_);
lean_dec_ref_known(v_a_3591_, 4);
v_n_3645_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_n_3645_);
v_isCumulative_3646_ = lean_ctor_get_uint8(v_b_3592_, sizeof(void*)*4 + 3);
v_d_3647_ = lean_ctor_get(v_b_3592_, 3);
lean_inc(v_d_3647_);
lean_dec_ref_known(v_b_3592_, 4);
v___x_3651_ = lean_nat_dec_eq(v_n_3642_, v_n_3645_);
lean_dec(v_n_3645_);
lean_dec(v_n_3642_);
if (v___x_3651_ == 0)
{
lean_dec(v_d_3647_);
lean_dec(v_d_3644_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
goto v___jp_3594_;
}
else
{
if (v_isCumulative_3646_ == 0)
{
if (v_isCumulative_3643_ == 0)
{
v___y_3649_ = v___x_3651_;
goto v___jp_3648_;
}
else
{
lean_dec(v_d_3647_);
lean_dec(v_d_3644_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
goto v___jp_3594_;
}
}
else
{
v___y_3649_ = v_isCumulative_3643_;
goto v___jp_3648_;
}
}
v___jp_3648_:
{
if (v___y_3649_ == 0)
{
lean_dec(v_d_3647_);
lean_dec(v_d_3644_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
goto v___jp_3594_;
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3644_, v_d_3647_, v_a_3593_);
return v___x_3650_;
}
}
}
else
{
lean_dec_ref_known(v_a_3591_, 4);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 7:
{
if (lean_obj_tag(v_b_3592_) == 7)
{
lean_object* v_d_3652_; lean_object* v_d_3653_; lean_object* v___x_3654_; 
v_d_3652_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3652_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3653_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3653_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3654_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3652_, v_d_3653_, v_a_3593_);
return v___x_3654_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 8:
{
if (lean_obj_tag(v_b_3592_) == 8)
{
uint8_t v_onlyNonCumulative_3655_; 
v_onlyNonCumulative_3655_ = lean_ctor_get_uint8(v_b_3592_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3655_ == 0)
{
uint8_t v_onlyNonCumulative_3656_; 
v_onlyNonCumulative_3656_ = lean_ctor_get_uint8(v_a_3591_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3656_ == 0)
{
lean_object* v_d_3657_; lean_object* v_d_3658_; lean_object* v___x_3659_; 
v_d_3657_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3657_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3658_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3658_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3659_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3657_, v_d_3658_, v_a_3593_);
return v___x_3659_;
}
else
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_dec_ref_known(v_b_3592_, 3);
lean_dec_ref_known(v_a_3591_, 3);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___x_3660_ = lean_box(v_onlyNonCumulative_3655_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v_a_3593_);
return v___x_3661_;
}
}
else
{
uint8_t v_onlyNonCumulative_3662_; 
v_onlyNonCumulative_3662_ = lean_ctor_get_uint8(v_a_3591_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
lean_dec_ref_known(v_b_3592_, 3);
lean_dec_ref_known(v_a_3591_, 3);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___x_3663_ = lean_box(v_onlyNonCumulative_3662_);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
lean_ctor_set(v___x_3664_, 1, v_a_3593_);
return v___x_3664_;
}
else
{
lean_object* v_d_3665_; lean_object* v_d_3666_; lean_object* v___x_3667_; 
v_d_3665_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3665_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3666_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3666_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3667_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3665_, v_d_3666_, v_a_3593_);
return v___x_3667_;
}
}
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 9:
{
if (lean_obj_tag(v_b_3592_) == 9)
{
lean_object* v_d_3668_; lean_object* v_d_3669_; lean_object* v___x_3670_; 
v_d_3668_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3668_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3669_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3669_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3670_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3668_, v_d_3669_, v_a_3593_);
return v___x_3670_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 10:
{
if (lean_obj_tag(v_b_3592_) == 10)
{
lean_object* v_d_3671_; lean_object* v_d_3672_; lean_object* v___x_3673_; 
v_d_3671_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3671_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3672_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3672_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3673_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3671_, v_d_3672_, v_a_3593_);
return v___x_3673_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 11:
{
if (lean_obj_tag(v_b_3592_) == 11)
{
lean_object* v_d_3674_; lean_object* v_d_3675_; lean_object* v___x_3676_; 
v_d_3674_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_d_3674_);
lean_dec_ref_known(v_a_3591_, 3);
v_d_3675_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_d_3675_);
lean_dec_ref_known(v_b_3592_, 3);
v___x_3676_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3674_, v_d_3675_, v_a_3593_);
return v___x_3676_;
}
else
{
lean_dec_ref_known(v_a_3591_, 3);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 12:
{
if (lean_obj_tag(v_b_3592_) == 12)
{
lean_object* v_p_3677_; lean_object* v_p_3678_; lean_object* v_d_3679_; lean_object* v_d_3680_; lean_object* v_id_3681_; lean_object* v_id_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3692_; 
v_p_3677_ = lean_ctor_get(v_a_3591_, 2);
lean_inc_ref(v_p_3677_);
v_p_3678_ = lean_ctor_get(v_b_3592_, 2);
lean_inc_ref(v_p_3678_);
v_d_3679_ = lean_ctor_get(v_a_3591_, 3);
lean_inc(v_d_3679_);
lean_dec_ref_known(v_a_3591_, 4);
v_d_3680_ = lean_ctor_get(v_b_3592_, 3);
lean_inc(v_d_3680_);
lean_dec_ref_known(v_b_3592_, 4);
v_id_3681_ = lean_ctor_get(v_p_3677_, 1);
lean_inc(v_id_3681_);
lean_dec_ref(v_p_3677_);
v_id_3682_ = lean_ctor_get(v_p_3678_, 1);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_p_3678_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v_p_3678_, 0);
lean_dec(v_unused_3693_);
v___x_3684_ = v_p_3678_;
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_id_3682_);
lean_dec(v_p_3678_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_name_eq(v_id_3681_, v_id_3682_);
lean_dec(v_id_3682_);
lean_dec(v_id_3681_);
if (v___x_3686_ == 0)
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
lean_dec(v_d_3680_);
lean_dec(v_d_3679_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___x_3687_ = lean_box(v___x_3686_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 1, v_a_3593_);
lean_ctor_set(v___x_3684_, 0, v___x_3687_);
v___x_3689_ = v___x_3684_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_a_3593_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
else
{
lean_object* v___x_3691_; 
lean_del_object(v___x_3684_);
v___x_3691_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3679_, v_d_3680_, v_a_3593_);
return v___x_3691_;
}
}
}
else
{
lean_dec_ref_known(v_a_3591_, 4);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 13:
{
if (lean_obj_tag(v_b_3592_) == 13)
{
lean_object* v_cost_3694_; lean_object* v_d_3695_; lean_object* v_cost_3696_; lean_object* v_d_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v_cost_3694_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_cost_3694_);
v_d_3695_ = lean_ctor_get(v_a_3591_, 3);
lean_inc(v_d_3695_);
lean_dec_ref_known(v_a_3591_, 4);
v_cost_3696_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_cost_3696_);
v_d_3697_ = lean_ctor_get(v_b_3592_, 3);
lean_inc(v_d_3697_);
lean_dec_ref_known(v_b_3592_, 4);
lean_inc_ref(v_inst_3589_);
v___x_3698_ = lean_apply_2(v_inst_3589_, v_cost_3694_, v_cost_3696_);
v___x_3699_ = lean_unbox(v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; 
lean_dec(v_d_3697_);
lean_dec(v_d_3695_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___x_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set(v___x_3700_, 1, v_a_3593_);
return v___x_3700_;
}
else
{
lean_object* v___x_3701_; 
v___x_3701_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_d_3695_, v_d_3697_, v_a_3593_);
return v___x_3701_;
}
}
else
{
lean_dec_ref_known(v_a_3591_, 4);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
case 14:
{
if (lean_obj_tag(v_b_3592_) == 14)
{
lean_object* v_a_3702_; lean_object* v_b_3703_; lean_object* v_a_3704_; lean_object* v_b_3705_; 
v_a_3702_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_a_3702_);
v_b_3703_ = lean_ctor_get(v_a_3591_, 3);
lean_inc(v_b_3703_);
lean_dec_ref_known(v_a_3591_, 4);
v_a_3704_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_a_3704_);
v_b_3705_ = lean_ctor_get(v_b_3592_, 3);
lean_inc(v_b_3705_);
lean_dec_ref_known(v_b_3592_, 4);
v_da1_3604_ = v_a_3702_;
v_da2_3605_ = v_b_3703_;
v_db1_3606_ = v_a_3704_;
v_db2_3607_ = v_b_3705_;
v___y_3608_ = v_a_3593_;
goto v___jp_3603_;
}
else
{
lean_dec_ref_known(v_a_3591_, 4);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
default: 
{
if (lean_obj_tag(v_b_3592_) == 15)
{
lean_object* v_a_3706_; lean_object* v_b_3707_; lean_object* v_a_3708_; lean_object* v_b_3709_; 
v_a_3706_ = lean_ctor_get(v_a_3591_, 2);
lean_inc(v_a_3706_);
v_b_3707_ = lean_ctor_get(v_a_3591_, 3);
lean_inc(v_b_3707_);
lean_dec_ref_known(v_a_3591_, 4);
v_a_3708_ = lean_ctor_get(v_b_3592_, 2);
lean_inc(v_a_3708_);
v_b_3709_ = lean_ctor_get(v_b_3592_, 3);
lean_inc(v_b_3709_);
lean_dec_ref_known(v_b_3592_, 4);
v_da1_3604_ = v_a_3706_;
v_da2_3605_ = v_b_3707_;
v_db1_3606_ = v_a_3708_;
v_db2_3607_ = v_b_3709_;
v___y_3608_ = v_a_3593_;
goto v___jp_3603_;
}
else
{
lean_dec_ref_known(v_a_3591_, 4);
lean_dec(v_b_3592_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
v___y_3599_ = v_a_3593_;
goto v___jp_3598_;
}
}
}
v___jp_3594_:
{
uint8_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = 0;
v___x_3596_ = lean_box(v___x_3595_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v_a_3593_);
return v___x_3597_;
}
v___jp_3598_:
{
uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3600_ = 0;
v___x_3601_ = lean_box(v___x_3600_);
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
lean_ctor_set(v___x_3602_, 1, v___y_3599_);
return v___x_3602_;
}
v___jp_3603_:
{
lean_object* v___x_3609_; lean_object* v_fst_3610_; uint8_t v___x_3611_; 
lean_inc_ref(v_inst_3590_);
lean_inc_ref(v_inst_3589_);
v___x_3609_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_da1_3604_, v_db1_3606_, v___y_3608_);
v_fst_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_fst_3610_);
v___x_3611_ = lean_unbox(v_fst_3610_);
lean_dec(v_fst_3610_);
if (v___x_3611_ == 0)
{
lean_dec(v_db2_3607_);
lean_dec(v_da2_3605_);
lean_dec_ref(v_inst_3590_);
lean_dec_ref(v_inst_3589_);
return v___x_3609_;
}
else
{
lean_object* v_snd_3612_; lean_object* v___x_3613_; 
v_snd_3612_ = lean_ctor_get(v___x_3609_, 1);
lean_inc(v_snd_3612_);
lean_dec_ref(v___x_3609_);
v___x_3613_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3589_, v_inst_3590_, v_da2_3605_, v_db2_3607_, v_snd_3612_);
return v___x_3613_;
}
}
v___jp_3614_:
{
uint8_t v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3618_ = lean_string_dec_eq(v_sa_3615_, v_sb_3616_);
lean_dec_ref(v_sb_3616_);
lean_dec_ref(v_sa_3615_);
v___x_3619_ = lean_box(v___x_3618_);
v___x_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___y_3617_);
return v___x_3620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(lean_object* v_inst_3710_, lean_object* v_inst_3711_, lean_object* v_a_3712_, lean_object* v_b_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v_cacheKey_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_inc(v_a_3712_);
v___x_3715_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3712_);
lean_inc(v_b_3713_);
v___x_3716_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3713_);
v_cacheKey_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3717_, 0, v___x_3715_);
lean_ctor_set(v_cacheKey_3717_, 1, v___x_3716_);
lean_inc_ref(v_inst_3710_);
v___x_3718_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_3718_, 0, lean_box(0));
lean_closure_set(v___x_3718_, 1, v_inst_3710_);
lean_inc_ref(v_inst_3711_);
v___x_3719_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_3719_, 0, lean_box(0));
lean_closure_set(v___x_3719_, 1, v_inst_3711_);
lean_inc_ref(v_cacheKey_3717_);
lean_inc_ref(v___x_3719_);
lean_inc_ref(v___x_3718_);
v___x_3720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_3718_, v___x_3719_, v_a_3714_, v_cacheKey_3717_);
if (lean_obj_tag(v___x_3720_) == 1)
{
lean_object* v_val_3721_; lean_object* v___x_3722_; 
lean_dec_ref(v___x_3719_);
lean_dec_ref(v___x_3718_);
lean_dec_ref_known(v_cacheKey_3717_, 2);
lean_dec(v_b_3713_);
lean_dec(v_a_3712_);
lean_dec_ref(v_inst_3711_);
lean_dec_ref(v_inst_3710_);
v_val_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_val_3721_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_val_3721_);
lean_ctor_set(v___x_3722_, 1, v_a_3714_);
return v___x_3722_;
}
else
{
lean_object* v___x_3723_; lean_object* v_fst_3724_; lean_object* v_snd_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3733_; 
lean_dec(v___x_3720_);
v___x_3723_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_3710_, v_inst_3711_, v_a_3712_, v_b_3713_, v_a_3714_);
v_fst_3724_ = lean_ctor_get(v___x_3723_, 0);
v_snd_3725_ = lean_ctor_get(v___x_3723_, 1);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3727_ = v___x_3723_;
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_snd_3725_);
lean_inc(v_fst_3724_);
lean_dec(v___x_3723_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
lean_inc(v_fst_3724_);
v___x_3729_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_3718_, v___x_3719_, v_snd_3725_, v_cacheKey_3717_, v_fst_3724_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 1, v___x_3729_);
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_fst_3724_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized(lean_object* v_00_u03c4_3734_, lean_object* v_inst_3735_, lean_object* v_inst_3736_, lean_object* v_a_3737_, lean_object* v_b_3738_, lean_object* v_a_3739_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3735_, v_inst_3736_, v_a_3737_, v_b_3738_, v_a_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go(lean_object* v_00_u03c4_3741_, lean_object* v_inst_3742_, lean_object* v_inst_3743_, lean_object* v_a_3744_, lean_object* v_b_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_3742_, v_inst_3743_, v_a_3744_, v_b_3745_, v_a_3746_);
return v___x_3747_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3748_ = lean_box(0);
v___x_3749_ = lean_unsigned_to_nat(16u);
v___x_3750_ = lean_mk_array(v___x_3749_, v___x_3748_);
return v___x_3750_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__1(void){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3751_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__0, &l_Lean_Fmt_Doc_beq___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__0);
v___x_3752_ = lean_unsigned_to_nat(0u);
v___x_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v___x_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___redArg(lean_object* v_inst_3754_, lean_object* v_inst_3755_, lean_object* v_a_3756_, lean_object* v_b_3757_){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v_fst_3760_; 
v___x_3758_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__1, &l_Lean_Fmt_Doc_beq___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__1);
v___x_3759_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3754_, v_inst_3755_, v_a_3756_, v_b_3757_, v___x_3758_);
v_fst_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_fst_3760_);
lean_dec_ref(v___x_3759_);
return v_fst_3760_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq(lean_object* v_00_u03c4_3761_, lean_object* v_inst_3762_, lean_object* v_inst_3763_, lean_object* v_a_3764_, lean_object* v_b_3765_){
_start:
{
lean_object* v___x_3766_; uint8_t v___x_3767_; 
v___x_3766_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_3762_, v_inst_3763_, v_a_3764_, v_b_3765_);
v___x_3767_ = lean_unbox(v___x_3766_);
lean_dec(v___x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___boxed(lean_object* v_00_u03c4_3768_, lean_object* v_inst_3769_, lean_object* v_inst_3770_, lean_object* v_a_3771_, lean_object* v_b_3772_){
_start:
{
uint8_t v_res_3773_; lean_object* v_r_3774_; 
v_res_3773_ = l_Lean_Fmt_Doc_beq(v_00_u03c4_3768_, v_inst_3769_, v_inst_3770_, v_a_3771_, v_b_3772_);
v_r_3774_ = lean_box(v_res_3773_);
return v_r_3774_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object* v_inst_3775_, lean_object* v_inst_3776_, lean_object* v_a_3777_, lean_object* v_b_3778_){
_start:
{
lean_object* v___x_3779_; uint8_t v___x_3780_; 
v___x_3779_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_3775_, v_inst_3776_, v_a_3777_, v_b_3778_);
v___x_3780_ = lean_unbox(v___x_3779_);
lean_dec(v___x_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0___boxed(lean_object* v_inst_3781_, lean_object* v_inst_3782_, lean_object* v_a_3783_, lean_object* v_b_3784_){
_start:
{
uint8_t v_res_3785_; lean_object* v_r_3786_; 
v_res_3785_ = l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(v_inst_3781_, v_inst_3782_, v_a_3783_, v_b_3784_);
v_r_3786_ = lean_box(v_res_3785_);
return v_r_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg(lean_object* v_inst_3787_, lean_object* v_inst_3788_){
_start:
{
lean_object* v___f_3789_; 
v___f_3789_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3789_, 0, v_inst_3787_);
lean_closure_set(v___f_3789_, 1, v_inst_3788_);
return v___f_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable(lean_object* v_00_u03c4_3790_, lean_object* v_inst_3791_, lean_object* v_inst_3792_){
_start:
{
lean_object* v___f_3793_; 
v___f_3793_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3793_, 0, v_inst_3791_);
lean_closure_set(v___f_3793_, 1, v_inst_3792_);
return v___f_3793_;
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

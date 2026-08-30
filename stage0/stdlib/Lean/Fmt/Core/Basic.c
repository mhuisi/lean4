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
uint8_t lean_uint8_land(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
lean_object* lean_array_to_list(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_mk(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullBefore(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullBefore___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullAfter(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullAfter___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullBefore(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullBefore___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullAfter(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullAfter___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_text___override___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_full___override___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full___override___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Fmt_Doc_full___override___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_full___override___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_Doc_full___override___redArg___closed__0 = (const lean_object*)&l_Lean_Fmt_Doc_full___override___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full___override(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Fmt.Doc.full"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__28 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__28_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__29 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__29_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__30 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__30_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Fmt.Doc.free"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__31 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__31_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__32 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__32_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__33 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__33_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.guarded"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__34 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__34_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__35 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__35_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__36 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__36_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__36_value),((lean_object*)&l_Lean_Fmt_instReprAssertion___lam__0___closed__1_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__37 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__37_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__38 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__38_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lean.Fmt.Doc.costing"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__39 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__39_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__40 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__40_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__41 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__41_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.either"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__42 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__42_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__43 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__43_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__44 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__44_value;
static const lean_string_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Fmt.Doc.append"};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__45 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__45_value)}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__46 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value;
static const lean_ctor_object l_Lean_Fmt_instReprDoc_repr___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__46_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___closed__47 = (const lean_object*)&l_Lean_Fmt_instReprDoc_repr___redArg___closed__47_value;
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
static const lean_closure_object l_Lean_Fmt_instAppendDoc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_Doc_append___override___redArg, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Fmt_instAppendDoc___closed__0 = (const lean_object*)&l_Lean_Fmt_instAppendDoc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_mk(uint8_t v_isFullBefore_22_, uint8_t v_isFullAfter_23_){
_start:
{
uint8_t v___x_24_; uint8_t v___x_25_; uint8_t v___x_26_; uint8_t v___x_27_; uint8_t v___x_28_; 
v___x_24_ = lean_bool_to_uint8(v_isFullBefore_22_);
v___x_25_ = 1;
v___x_26_ = lean_uint8_shift_left(v___x_24_, v___x_25_);
v___x_27_ = lean_bool_to_uint8(v_isFullAfter_23_);
v___x_28_ = lean_uint8_lor(v___x_26_, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_mk___boxed(lean_object* v_isFullBefore_29_, lean_object* v_isFullAfter_30_){
_start:
{
uint8_t v_isFullBefore_boxed_31_; uint8_t v_isFullAfter_boxed_32_; uint8_t v_res_33_; lean_object* v_r_34_; 
v_isFullBefore_boxed_31_ = lean_unbox(v_isFullBefore_29_);
v_isFullAfter_boxed_32_ = lean_unbox(v_isFullAfter_30_);
v_res_33_ = l_Lean_Fmt_FullnessState_mk(v_isFullBefore_boxed_31_, v_isFullAfter_boxed_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullBefore(uint8_t v_s_35_){
_start:
{
uint8_t v___x_36_; uint8_t v___x_37_; uint8_t v___x_38_; uint8_t v___x_39_; 
v___x_36_ = 2;
v___x_37_ = lean_uint8_land(v_s_35_, v___x_36_);
v___x_38_ = 0;
v___x_39_ = lean_uint8_dec_eq(v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 1;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = 0;
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullBefore___boxed(lean_object* v_s_42_){
_start:
{
uint8_t v_s_boxed_43_; uint8_t v_res_44_; lean_object* v_r_45_; 
v_s_boxed_43_ = lean_unbox(v_s_42_);
v_res_44_ = l_Lean_Fmt_FullnessState_isFullBefore(v_s_boxed_43_);
v_r_45_ = lean_box(v_res_44_);
return v_r_45_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_isFullAfter(uint8_t v_s_46_){
_start:
{
uint8_t v___x_47_; uint8_t v___x_48_; uint8_t v___x_49_; uint8_t v___x_50_; 
v___x_47_ = 1;
v___x_48_ = lean_uint8_land(v_s_46_, v___x_47_);
v___x_49_ = 0;
v___x_50_ = lean_uint8_dec_eq(v___x_48_, v___x_49_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_isFullAfter___boxed(lean_object* v_s_53_){
_start:
{
uint8_t v_s_boxed_54_; uint8_t v_res_55_; lean_object* v_r_56_; 
v_s_boxed_54_ = lean_unbox(v_s_53_);
v_res_55_ = l_Lean_Fmt_FullnessState_isFullAfter(v_s_boxed_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullBefore(uint8_t v_s_57_, uint8_t v_isFullBefore_58_){
_start:
{
uint8_t v___x_59_; uint8_t v___x_60_; uint8_t v___x_61_; uint8_t v___x_62_; uint8_t v___x_63_; uint8_t v___x_64_; 
v___x_59_ = 253;
v___x_60_ = lean_uint8_land(v_s_57_, v___x_59_);
v___x_61_ = lean_bool_to_uint8(v_isFullBefore_58_);
v___x_62_ = 1;
v___x_63_ = lean_uint8_shift_left(v___x_61_, v___x_62_);
v___x_64_ = lean_uint8_lor(v___x_60_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullBefore___boxed(lean_object* v_s_65_, lean_object* v_isFullBefore_66_){
_start:
{
uint8_t v_s_boxed_67_; uint8_t v_isFullBefore_boxed_68_; uint8_t v_res_69_; lean_object* v_r_70_; 
v_s_boxed_67_ = lean_unbox(v_s_65_);
v_isFullBefore_boxed_68_ = lean_unbox(v_isFullBefore_66_);
v_res_69_ = l_Lean_Fmt_FullnessState_setFullBefore(v_s_boxed_67_, v_isFullBefore_boxed_68_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_FullnessState_setFullAfter(uint8_t v_s_71_, uint8_t v_isFullAfter_72_){
_start:
{
uint8_t v___x_73_; uint8_t v___x_74_; uint8_t v___x_75_; uint8_t v___x_76_; 
v___x_73_ = 254;
v___x_74_ = lean_uint8_land(v_s_71_, v___x_73_);
v___x_75_ = lean_bool_to_uint8(v_isFullAfter_72_);
v___x_76_ = lean_uint8_lor(v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_FullnessState_setFullAfter___boxed(lean_object* v_s_77_, lean_object* v_isFullAfter_78_){
_start:
{
uint8_t v_s_boxed_79_; uint8_t v_isFullAfter_boxed_80_; uint8_t v_res_81_; lean_object* v_r_82_; 
v_s_boxed_79_ = lean_unbox(v_s_77_);
v_isFullAfter_boxed_80_ = lean_unbox(v_isFullAfter_78_);
v_res_81_ = l_Lean_Fmt_FullnessState_setFullAfter(v_s_boxed_79_, v_isFullAfter_boxed_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId___aux__1(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_unsigned_to_nat(0u);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Fmt_instInhabitedTagId(void){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_unsigned_to_nat(0u);
return v___x_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqTagId___aux__1(lean_object* v_a_85_, lean_object* v_b_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = lean_nat_dec_eq(v_a_85_, v_b_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqTagId___aux__1___boxed(lean_object* v_a_88_, lean_object* v_b_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Lean_Fmt_instBEqTagId___aux__1(v_a_88_, v_b_89_);
lean_dec(v_b_89_);
lean_dec(v_a_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableTagId___aux__1(lean_object* v_n_94_){
_start:
{
uint64_t v___x_95_; 
v___x_95_ = lean_uint64_of_nat(v_n_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableTagId___aux__1___boxed(lean_object* v_n_96_){
_start:
{
uint64_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_Fmt_instHashableTagId___aux__1(v_n_96_);
lean_dec(v_n_96_);
v_r_98_ = lean_box_uint64(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___aux__1(lean_object* v_x_101_, lean_object* v_y_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_lt(v_x_101_, v_y_102_);
if (v___x_103_ == 0)
{
uint8_t v___x_104_; 
v___x_104_ = lean_nat_dec_eq(v_x_101_, v_y_102_);
if (v___x_104_ == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 2;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___aux__1___boxed(lean_object* v_x_108_, lean_object* v_y_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Lean_Fmt_instOrdTagId___aux__1(v_x_108_, v_y_109_);
lean_dec(v_y_109_);
lean_dec(v_x_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instOrdTagId___lam__0(lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = lean_nat_dec_lt(v___y_112_, v___y_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = lean_nat_dec_eq(v___y_112_, v___y_113_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; 
v___x_116_ = 2;
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 1;
return v___x_117_;
}
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instOrdTagId___lam__0___boxed(lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Lean_Fmt_instOrdTagId___lam__0(v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec(v___y_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___redArg(lean_object* v_n_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = l_Nat_reprFast(v_n_125_);
v___x_127_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1(lean_object* v_n_128_, lean_object* v_x_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = l_Nat_reprFast(v_n_128_);
v___x_131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___aux__1___boxed(lean_object* v_n_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Fmt_instReprTagId___aux__1(v_n_132_, v_x_133_);
lean_dec(v_x_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0(lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = l_Nat_reprFast(v___y_135_);
v___x_138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprTagId___lam__0___boxed(lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Fmt_instReprTagId___lam__0(v___y_139_, v___y_140_);
lean_dec(v___y_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instToStringTagId___aux__1(lean_object* v_n_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Nat_reprFast(v_n_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_nat_add(v_a_148_, v_b_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHAddTagIdNat___aux__1___boxed(lean_object* v_a_151_, lean_object* v_b_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Fmt_instHAddTagIdNat___aux__1(v_a_151_, v_b_152_);
lean_dec(v_b_152_);
lean_dec(v_a_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx(uint8_t v_x_156_){
_start:
{
switch(v_x_156_)
{
case 0:
{
lean_object* v___x_157_; 
v___x_157_ = lean_unsigned_to_nat(0u);
return v___x_157_;
}
case 1:
{
lean_object* v___x_158_; 
v___x_158_ = lean_unsigned_to_nat(1u);
return v___x_158_;
}
default: 
{
lean_object* v___x_159_; 
v___x_159_ = lean_unsigned_to_nat(2u);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_x_boxed_161_; lean_object* v_res_162_; 
v_x_boxed_161_ = lean_unbox(v_x_160_);
v_res_162_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorIdx(v_x_boxed_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(lean_object* v_k_163_){
_start:
{
lean_inc(v_k_163_);
return v_k_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg___boxed(lean_object* v_k_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___redArg(v_k_164_);
lean_dec(v_k_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(lean_object* v_motive_166_, lean_object* v_ctorIdx_167_, uint8_t v_t_168_, lean_object* v_h_169_, lean_object* v_k_170_){
_start:
{
lean_inc(v_k_170_);
return v_k_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim___boxed(lean_object* v_motive_171_, lean_object* v_ctorIdx_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_k_175_){
_start:
{
uint8_t v_t_boxed_176_; lean_object* v_res_177_; 
v_t_boxed_176_ = lean_unbox(v_t_173_);
v_res_177_ = l_Lean_Fmt_Doc_AlwaysEmptiness_ctorElim(v_motive_171_, v_ctorIdx_172_, v_t_boxed_176_, v_h_174_, v_k_175_);
lean_dec(v_k_175_);
lean_dec(v_ctorIdx_172_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(lean_object* v_alwaysEmpty_178_){
_start:
{
lean_inc(v_alwaysEmpty_178_);
return v_alwaysEmpty_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg___boxed(lean_object* v_alwaysEmpty_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___redArg(v_alwaysEmpty_179_);
lean_dec(v_alwaysEmpty_179_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(lean_object* v_motive_181_, uint8_t v_t_182_, lean_object* v_h_183_, lean_object* v_alwaysEmpty_184_){
_start:
{
lean_inc(v_alwaysEmpty_184_);
return v_alwaysEmpty_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim___boxed(lean_object* v_motive_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_alwaysEmpty_188_){
_start:
{
uint8_t v_t_boxed_189_; lean_object* v_res_190_; 
v_t_boxed_189_ = lean_unbox(v_t_186_);
v_res_190_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmpty_elim(v_motive_185_, v_t_boxed_189_, v_h_187_, v_alwaysEmpty_188_);
lean_dec(v_alwaysEmpty_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(lean_object* v_alwaysEmptyIfFlattened_191_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_191_);
return v_alwaysEmptyIfFlattened_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg___boxed(lean_object* v_alwaysEmptyIfFlattened_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___redArg(v_alwaysEmptyIfFlattened_192_);
lean_dec(v_alwaysEmptyIfFlattened_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(lean_object* v_motive_194_, uint8_t v_t_195_, lean_object* v_h_196_, lean_object* v_alwaysEmptyIfFlattened_197_){
_start:
{
lean_inc(v_alwaysEmptyIfFlattened_197_);
return v_alwaysEmptyIfFlattened_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim___boxed(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_alwaysEmptyIfFlattened_201_){
_start:
{
uint8_t v_t_boxed_202_; lean_object* v_res_203_; 
v_t_boxed_202_ = lean_unbox(v_t_199_);
v_res_203_ = l_Lean_Fmt_Doc_AlwaysEmptiness_alwaysEmptyIfFlattened_elim(v_motive_198_, v_t_boxed_202_, v_h_200_, v_alwaysEmptyIfFlattened_201_);
lean_dec(v_alwaysEmptyIfFlattened_201_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(lean_object* v_sometimesNonEmpty_204_){
_start:
{
lean_inc(v_sometimesNonEmpty_204_);
return v_sometimesNonEmpty_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg___boxed(lean_object* v_sometimesNonEmpty_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___redArg(v_sometimesNonEmpty_205_);
lean_dec(v_sometimesNonEmpty_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(lean_object* v_motive_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_sometimesNonEmpty_210_){
_start:
{
lean_inc(v_sometimesNonEmpty_210_);
return v_sometimesNonEmpty_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_sometimesNonEmpty_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lean_Fmt_Doc_AlwaysEmptiness_sometimesNonEmpty_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_sometimesNonEmpty_214_);
lean_dec(v_sometimesNonEmpty_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(uint8_t v_x_217_){
_start:
{
switch(v_x_217_)
{
case 0:
{
lean_object* v___x_218_; 
v___x_218_ = lean_unsigned_to_nat(0u);
return v___x_218_;
}
case 1:
{
lean_object* v___x_219_; 
v___x_219_ = lean_unsigned_to_nat(1u);
return v___x_219_;
}
default: 
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(2u);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0___boxed(lean_object* v_x_221_){
_start:
{
uint8_t v_x_69__boxed_222_; lean_object* v_res_223_; 
v_x_69__boxed_222_ = lean_unbox(v_x_221_);
v_res_223_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_x_69__boxed_222_);
return v_res_223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysEmptiness_max(uint8_t v_e1_224_, uint8_t v_e2_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e2_225_);
v___x_227_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max___lam__0(v_e1_224_);
v___x_228_ = lean_nat_dec_le(v___x_226_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v___x_226_);
if (v___x_228_ == 0)
{
return v_e2_225_;
}
else
{
return v_e1_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysEmptiness_max___boxed(lean_object* v_e1_229_, lean_object* v_e2_230_){
_start:
{
uint8_t v_e1_boxed_231_; uint8_t v_e2_boxed_232_; uint8_t v_res_233_; lean_object* v_r_234_; 
v_e1_boxed_231_ = lean_unbox(v_e1_229_);
v_e2_boxed_232_ = lean_unbox(v_e2_230_);
v_res_233_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v_e1_boxed_231_, v_e2_boxed_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx(uint8_t v_x_235_){
_start:
{
if (v_x_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = lean_unsigned_to_nat(0u);
return v___x_236_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(1u);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx___boxed(lean_object* v_x_238_){
_start:
{
uint8_t v_x_boxed_239_; lean_object* v_res_240_; 
v_x_boxed_239_ = lean_unbox(v_x_238_);
v_res_240_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorIdx(v_x_boxed_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(lean_object* v_k_241_){
_start:
{
lean_inc(v_k_241_);
return v_k_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg___boxed(lean_object* v_k_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___redArg(v_k_242_);
lean_dec(v_k_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(lean_object* v_motive_244_, lean_object* v_ctorIdx_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_k_248_){
_start:
{
lean_inc(v_k_248_);
return v_k_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim___boxed(lean_object* v_motive_249_, lean_object* v_ctorIdx_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_k_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_ctorElim(v_motive_249_, v_ctorIdx_250_, v_t_boxed_254_, v_h_252_, v_k_253_);
lean_dec(v_k_253_);
lean_dec(v_ctorIdx_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(lean_object* v_alwaysNonEmpty_256_){
_start:
{
lean_inc(v_alwaysNonEmpty_256_);
return v_alwaysNonEmpty_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg___boxed(lean_object* v_alwaysNonEmpty_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___redArg(v_alwaysNonEmpty_257_);
lean_dec(v_alwaysNonEmpty_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_alwaysNonEmpty_262_){
_start:
{
lean_inc(v_alwaysNonEmpty_262_);
return v_alwaysNonEmpty_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_alwaysNonEmpty_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_alwaysNonEmpty_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_alwaysNonEmpty_266_);
lean_dec(v_alwaysNonEmpty_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(lean_object* v_sometimesEmpty_269_){
_start:
{
lean_inc(v_sometimesEmpty_269_);
return v_sometimesEmpty_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg___boxed(lean_object* v_sometimesEmpty_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___redArg(v_sometimesEmpty_270_);
lean_dec(v_sometimesEmpty_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(lean_object* v_motive_272_, uint8_t v_t_273_, lean_object* v_h_274_, lean_object* v_sometimesEmpty_275_){
_start:
{
lean_inc(v_sometimesEmpty_275_);
return v_sometimesEmpty_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim___boxed(lean_object* v_motive_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_sometimesEmpty_279_){
_start:
{
uint8_t v_t_boxed_280_; lean_object* v_res_281_; 
v_t_boxed_280_ = lean_unbox(v_t_277_);
v_res_281_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_sometimesEmpty_elim(v_motive_276_, v_t_boxed_280_, v_h_278_, v_sometimesEmpty_279_);
lean_dec(v_sometimesEmpty_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(uint8_t v_x_282_){
_start:
{
if (v_x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_unsigned_to_nat(0u);
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_unsigned_to_nat(1u);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0___boxed(lean_object* v_x_285_){
_start:
{
uint8_t v_x_51__boxed_286_; lean_object* v_res_287_; 
v_x_51__boxed_286_ = lean_unbox(v_x_285_);
v_res_287_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_x_51__boxed_286_);
return v_res_287_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(uint8_t v_e1_288_, uint8_t v_e2_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_290_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e2_289_);
v___x_291_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___lam__0(v_e1_288_);
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
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_AlwaysNonEmptiness_max___boxed(lean_object* v_e1_293_, lean_object* v_e2_294_){
_start:
{
uint8_t v_e1_boxed_295_; uint8_t v_e2_boxed_296_; uint8_t v_res_297_; lean_object* v_r_298_; 
v_e1_boxed_295_ = lean_unbox(v_e1_293_);
v_e2_boxed_296_ = lean_unbox(v_e2_294_);
v_res_297_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v_e1_boxed_295_, v_e2_boxed_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx(uint8_t v_x_299_){
_start:
{
switch(v_x_299_)
{
case 0:
{
lean_object* v___x_300_; 
v___x_300_ = lean_unsigned_to_nat(0u);
return v___x_300_;
}
case 1:
{
lean_object* v___x_301_; 
v___x_301_ = lean_unsigned_to_nat(1u);
return v___x_301_;
}
case 2:
{
lean_object* v___x_302_; 
v___x_302_ = lean_unsigned_to_nat(2u);
return v___x_302_;
}
case 3:
{
lean_object* v___x_303_; 
v___x_303_ = lean_unsigned_to_nat(3u);
return v___x_303_;
}
default: 
{
lean_object* v___x_304_; 
v___x_304_ = lean_unsigned_to_nat(4u);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorIdx___boxed(lean_object* v_x_305_){
_start:
{
uint8_t v_x_boxed_306_; lean_object* v_res_307_; 
v_x_boxed_306_ = lean_unbox(v_x_305_);
v_res_307_ = l_Lean_Fmt_Doc_Atomicness_ctorIdx(v_x_boxed_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(lean_object* v_k_308_){
_start:
{
lean_inc(v_k_308_);
return v_k_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg___boxed(lean_object* v_k_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Fmt_Doc_Atomicness_ctorElim___redArg(v_k_309_);
lean_dec(v_k_309_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim(lean_object* v_motive_311_, lean_object* v_ctorIdx_312_, uint8_t v_t_313_, lean_object* v_h_314_, lean_object* v_k_315_){
_start:
{
lean_inc(v_k_315_);
return v_k_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_ctorElim___boxed(lean_object* v_motive_316_, lean_object* v_ctorIdx_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_k_320_){
_start:
{
uint8_t v_t_boxed_321_; lean_object* v_res_322_; 
v_t_boxed_321_ = lean_unbox(v_t_318_);
v_res_322_ = l_Lean_Fmt_Doc_Atomicness_ctorElim(v_motive_316_, v_ctorIdx_317_, v_t_boxed_321_, v_h_319_, v_k_320_);
lean_dec(v_k_320_);
lean_dec(v_ctorIdx_317_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(lean_object* v_atomic_323_){
_start:
{
lean_inc(v_atomic_323_);
return v_atomic_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg___boxed(lean_object* v_atomic_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim___redArg(v_atomic_324_);
lean_dec(v_atomic_324_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim(lean_object* v_motive_326_, uint8_t v_t_327_, lean_object* v_h_328_, lean_object* v_atomic_329_){
_start:
{
lean_inc(v_atomic_329_);
return v_atomic_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomic_elim___boxed(lean_object* v_motive_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_atomic_333_){
_start:
{
uint8_t v_t_boxed_334_; lean_object* v_res_335_; 
v_t_boxed_334_ = lean_unbox(v_t_331_);
v_res_335_ = l_Lean_Fmt_Doc_Atomicness_atomic_elim(v_motive_330_, v_t_boxed_334_, v_h_332_, v_atomic_333_);
lean_dec(v_atomic_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(lean_object* v_atomicIfFlattened_336_){
_start:
{
lean_inc(v_atomicIfFlattened_336_);
return v_atomicIfFlattened_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg___boxed(lean_object* v_atomicIfFlattened_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___redArg(v_atomicIfFlattened_337_);
lean_dec(v_atomicIfFlattened_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(lean_object* v_motive_339_, uint8_t v_t_340_, lean_object* v_h_341_, lean_object* v_atomicIfFlattened_342_){
_start:
{
lean_inc(v_atomicIfFlattened_342_);
return v_atomicIfFlattened_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim___boxed(lean_object* v_motive_343_, lean_object* v_t_344_, lean_object* v_h_345_, lean_object* v_atomicIfFlattened_346_){
_start:
{
uint8_t v_t_boxed_347_; lean_object* v_res_348_; 
v_t_boxed_347_ = lean_unbox(v_t_344_);
v_res_348_ = l_Lean_Fmt_Doc_Atomicness_atomicIfFlattened_elim(v_motive_343_, v_t_boxed_347_, v_h_345_, v_atomicIfFlattened_346_);
lean_dec(v_atomicIfFlattened_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(lean_object* v_compoundAtomic_349_){
_start:
{
lean_inc(v_compoundAtomic_349_);
return v_compoundAtomic_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg___boxed(lean_object* v_compoundAtomic_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___redArg(v_compoundAtomic_350_);
lean_dec(v_compoundAtomic_350_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(lean_object* v_motive_352_, uint8_t v_t_353_, lean_object* v_h_354_, lean_object* v_compoundAtomic_355_){
_start:
{
lean_inc(v_compoundAtomic_355_);
return v_compoundAtomic_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim___boxed(lean_object* v_motive_356_, lean_object* v_t_357_, lean_object* v_h_358_, lean_object* v_compoundAtomic_359_){
_start:
{
uint8_t v_t_boxed_360_; lean_object* v_res_361_; 
v_t_boxed_360_ = lean_unbox(v_t_357_);
v_res_361_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomic_elim(v_motive_356_, v_t_boxed_360_, v_h_358_, v_compoundAtomic_359_);
lean_dec(v_compoundAtomic_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(lean_object* v_compoundAtomicIfFlattened_362_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_362_);
return v_compoundAtomicIfFlattened_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg___boxed(lean_object* v_compoundAtomicIfFlattened_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___redArg(v_compoundAtomicIfFlattened_363_);
lean_dec(v_compoundAtomicIfFlattened_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(lean_object* v_motive_365_, uint8_t v_t_366_, lean_object* v_h_367_, lean_object* v_compoundAtomicIfFlattened_368_){
_start:
{
lean_inc(v_compoundAtomicIfFlattened_368_);
return v_compoundAtomicIfFlattened_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim___boxed(lean_object* v_motive_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_compoundAtomicIfFlattened_372_){
_start:
{
uint8_t v_t_boxed_373_; lean_object* v_res_374_; 
v_t_boxed_373_ = lean_unbox(v_t_370_);
v_res_374_ = l_Lean_Fmt_Doc_Atomicness_compoundAtomicIfFlattened_elim(v_motive_369_, v_t_boxed_373_, v_h_371_, v_compoundAtomicIfFlattened_372_);
lean_dec(v_compoundAtomicIfFlattened_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(lean_object* v_nonAtomic_375_){
_start:
{
lean_inc(v_nonAtomic_375_);
return v_nonAtomic_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg___boxed(lean_object* v_nonAtomic_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___redArg(v_nonAtomic_376_);
lean_dec(v_nonAtomic_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(lean_object* v_motive_378_, uint8_t v_t_379_, lean_object* v_h_380_, lean_object* v_nonAtomic_381_){
_start:
{
lean_inc(v_nonAtomic_381_);
return v_nonAtomic_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim___boxed(lean_object* v_motive_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_nonAtomic_385_){
_start:
{
uint8_t v_t_boxed_386_; lean_object* v_res_387_; 
v_t_boxed_386_ = lean_unbox(v_t_383_);
v_res_387_ = l_Lean_Fmt_Doc_Atomicness_nonAtomic_elim(v_motive_382_, v_t_boxed_386_, v_h_384_, v_nonAtomic_385_);
lean_dec(v_nonAtomic_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0(uint8_t v_x_388_){
_start:
{
switch(v_x_388_)
{
case 0:
{
lean_object* v___x_389_; 
v___x_389_ = lean_unsigned_to_nat(0u);
return v___x_389_;
}
case 1:
{
lean_object* v___x_390_; 
v___x_390_ = lean_unsigned_to_nat(1u);
return v___x_390_;
}
case 2:
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(2u);
return v___x_391_;
}
case 3:
{
lean_object* v___x_392_; 
v___x_392_ = lean_unsigned_to_nat(3u);
return v___x_392_;
}
default: 
{
lean_object* v___x_393_; 
v___x_393_ = lean_unsigned_to_nat(4u);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___lam__0___boxed(lean_object* v_x_394_){
_start:
{
uint8_t v_x_105__boxed_395_; lean_object* v_res_396_; 
v_x_105__boxed_395_ = lean_unbox(v_x_394_);
v_res_396_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_x_105__boxed_395_);
return v_res_396_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_Atomicness_max(uint8_t v_e1_397_, uint8_t v_e2_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e2_398_);
v___x_400_ = l_Lean_Fmt_Doc_Atomicness_max___lam__0(v_e1_397_);
v___x_401_ = lean_nat_dec_le(v___x_399_, v___x_400_);
lean_dec(v___x_400_);
lean_dec(v___x_399_);
if (v___x_401_ == 0)
{
return v_e2_398_;
}
else
{
return v_e1_397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_Atomicness_max___boxed(lean_object* v_e1_402_, lean_object* v_e2_403_){
_start:
{
uint8_t v_e1_boxed_404_; uint8_t v_e2_boxed_405_; uint8_t v_res_406_; lean_object* v_r_407_; 
v_e1_boxed_404_ = lean_unbox(v_e1_402_);
v_e2_boxed_405_ = lean_unbox(v_e2_403_);
v_res_406_ = l_Lean_Fmt_Doc_Atomicness_max(v_e1_boxed_404_, v_e2_boxed_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0(lean_object* v_x_411_, lean_object* v_x_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = ((lean_object*)(l_Lean_Fmt_instReprAssertion___lam__0___closed__1));
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprAssertion___lam__0___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Fmt_instReprAssertion___lam__0(v_x_414_, v_x_415_);
lean_dec(v_x_415_);
lean_dec_ref(v_x_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg(lean_object* v_x_419_){
_start:
{
switch(lean_obj_tag(v_x_419_))
{
case 0:
{
lean_object* v___x_420_; 
v___x_420_ = lean_unsigned_to_nat(0u);
return v___x_420_;
}
case 1:
{
lean_object* v___x_421_; 
v___x_421_ = lean_unsigned_to_nat(1u);
return v___x_421_;
}
case 2:
{
lean_object* v___x_422_; 
v___x_422_ = lean_unsigned_to_nat(2u);
return v___x_422_;
}
case 3:
{
lean_object* v___x_423_; 
v___x_423_ = lean_unsigned_to_nat(3u);
return v___x_423_;
}
case 4:
{
lean_object* v___x_424_; 
v___x_424_ = lean_unsigned_to_nat(4u);
return v___x_424_;
}
case 5:
{
lean_object* v___x_425_; 
v___x_425_ = lean_unsigned_to_nat(5u);
return v___x_425_;
}
case 6:
{
lean_object* v___x_426_; 
v___x_426_ = lean_unsigned_to_nat(6u);
return v___x_426_;
}
case 7:
{
lean_object* v___x_427_; 
v___x_427_ = lean_unsigned_to_nat(7u);
return v___x_427_;
}
case 8:
{
lean_object* v___x_428_; 
v___x_428_ = lean_unsigned_to_nat(8u);
return v___x_428_;
}
case 9:
{
lean_object* v___x_429_; 
v___x_429_ = lean_unsigned_to_nat(9u);
return v___x_429_;
}
case 10:
{
lean_object* v___x_430_; 
v___x_430_ = lean_unsigned_to_nat(10u);
return v___x_430_;
}
case 11:
{
lean_object* v___x_431_; 
v___x_431_ = lean_unsigned_to_nat(11u);
return v___x_431_;
}
case 12:
{
lean_object* v___x_432_; 
v___x_432_ = lean_unsigned_to_nat(12u);
return v___x_432_;
}
case 13:
{
lean_object* v___x_433_; 
v___x_433_ = lean_unsigned_to_nat(13u);
return v___x_433_;
}
default: 
{
lean_object* v___x_434_; 
v___x_434_ = lean_unsigned_to_nat(14u);
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___redArg___boxed(lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Fmt_Doc_ctorIdx___redArg(v_x_435_);
lean_dec(v_x_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx(lean_object* v_00_u03c4_437_, lean_object* v_x_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Fmt_Doc_ctorIdx___redArg(v_x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorIdx___boxed(lean_object* v_00_u03c4_440_, lean_object* v_x_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Fmt_Doc_ctorIdx(v_00_u03c4_440_, v_x_441_);
lean_dec(v_x_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___redArg(lean_object* v_t_443_, lean_object* v_k_444_){
_start:
{
switch(lean_obj_tag(v_t_443_))
{
case 0:
{
return v_k_444_;
}
case 1:
{
lean_object* v_f_445_; lean_object* v___x_446_; 
v_f_445_ = lean_ctor_get(v_t_443_, 0);
lean_inc_ref(v_f_445_);
lean_dec_ref_known(v_t_443_, 1);
v___x_446_ = lean_apply_1(v_k_444_, v_f_445_);
return v___x_446_;
}
case 2:
{
lean_object* v_s_447_; lean_object* v___x_448_; 
v_s_447_ = lean_ctor_get(v_t_443_, 0);
lean_inc_ref(v_s_447_);
lean_dec_ref_known(v_t_443_, 1);
v___x_448_ = lean_apply_1(v_k_444_, v_s_447_);
return v___x_448_;
}
case 3:
{
lean_object* v_id_449_; lean_object* v_d_450_; lean_object* v___x_451_; 
v_id_449_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_id_449_);
v_d_450_ = lean_ctor_get(v_t_443_, 1);
lean_inc(v_d_450_);
lean_dec_ref_known(v_t_443_, 2);
v___x_451_ = lean_apply_2(v_k_444_, v_id_449_, v_d_450_);
return v___x_451_;
}
case 6:
{
lean_object* v_n_452_; uint8_t v_isCumulative_453_; lean_object* v_d_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v_n_452_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_n_452_);
v_isCumulative_453_ = lean_ctor_get_uint8(v_t_443_, sizeof(void*)*2);
v_d_454_ = lean_ctor_get(v_t_443_, 1);
lean_inc(v_d_454_);
lean_dec_ref_known(v_t_443_, 2);
v___x_455_ = lean_box(v_isCumulative_453_);
v___x_456_ = lean_apply_3(v_k_444_, v_n_452_, v___x_455_, v_d_454_);
return v___x_456_;
}
case 8:
{
uint8_t v_onlyNonCumulative_457_; lean_object* v_d_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v_onlyNonCumulative_457_ = lean_ctor_get_uint8(v_t_443_, sizeof(void*)*1);
v_d_458_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_d_458_);
lean_dec_ref_known(v_t_443_, 1);
v___x_459_ = lean_box(v_onlyNonCumulative_457_);
v___x_460_ = lean_apply_2(v_k_444_, v___x_459_, v_d_458_);
return v___x_460_;
}
case 11:
{
lean_object* v_p_461_; lean_object* v_d_462_; lean_object* v___x_463_; 
v_p_461_ = lean_ctor_get(v_t_443_, 0);
lean_inc_ref(v_p_461_);
v_d_462_ = lean_ctor_get(v_t_443_, 1);
lean_inc(v_d_462_);
lean_dec_ref_known(v_t_443_, 2);
v___x_463_ = lean_apply_2(v_k_444_, v_p_461_, v_d_462_);
return v___x_463_;
}
case 12:
{
lean_object* v_cost_464_; lean_object* v_d_465_; lean_object* v___x_466_; 
v_cost_464_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_cost_464_);
v_d_465_ = lean_ctor_get(v_t_443_, 1);
lean_inc(v_d_465_);
lean_dec_ref_known(v_t_443_, 2);
v___x_466_ = lean_apply_2(v_k_444_, v_cost_464_, v_d_465_);
return v___x_466_;
}
case 13:
{
lean_object* v_a_467_; lean_object* v_b_468_; lean_object* v___x_469_; 
v_a_467_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_a_467_);
v_b_468_ = lean_ctor_get(v_t_443_, 1);
lean_inc(v_b_468_);
lean_dec_ref_known(v_t_443_, 2);
v___x_469_ = lean_apply_2(v_k_444_, v_a_467_, v_b_468_);
return v___x_469_;
}
case 14:
{
lean_object* v_a_470_; lean_object* v_b_471_; lean_object* v___x_472_; 
v_a_470_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_a_470_);
v_b_471_ = lean_ctor_get(v_t_443_, 1);
lean_inc(v_b_471_);
lean_dec_ref_known(v_t_443_, 2);
v___x_472_ = lean_apply_2(v_k_444_, v_a_470_, v_b_471_);
return v___x_472_;
}
default: 
{
lean_object* v_d_473_; lean_object* v___x_474_; 
v_d_473_ = lean_ctor_get(v_t_443_, 0);
lean_inc(v_d_473_);
lean_dec(v_t_443_);
v___x_474_ = lean_apply_1(v_k_444_, v_d_473_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim(lean_object* v_00_u03c4_475_, lean_object* v_motive_476_, lean_object* v_ctorIdx_477_, lean_object* v_t_478_, lean_object* v_h_479_, lean_object* v_k_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_478_, v_k_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_ctorElim___boxed(lean_object* v_00_u03c4_482_, lean_object* v_motive_483_, lean_object* v_ctorIdx_484_, lean_object* v_t_485_, lean_object* v_h_486_, lean_object* v_k_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Fmt_Doc_ctorElim(v_00_u03c4_482_, v_motive_483_, v_ctorIdx_484_, v_t_485_, v_h_486_, v_k_487_);
lean_dec(v_ctorIdx_484_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim___redArg(lean_object* v_t_489_, lean_object* v_failure_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_489_, v_failure_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure_elim(lean_object* v_00_u03c4_492_, lean_object* v_motive_493_, lean_object* v_t_494_, lean_object* v_h_495_, lean_object* v_failure_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_494_, v_failure_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim___redArg(lean_object* v_t_498_, lean_object* v_newline_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_498_, v_newline_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline_elim(lean_object* v_00_u03c4_501_, lean_object* v_motive_502_, lean_object* v_t_503_, lean_object* v_h_504_, lean_object* v_newline_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_503_, v_newline_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim___redArg(lean_object* v_t_507_, lean_object* v_text_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_507_, v_text_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text_elim(lean_object* v_00_u03c4_510_, lean_object* v_motive_511_, lean_object* v_t_512_, lean_object* v_h_513_, lean_object* v_text_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_512_, v_text_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim___redArg(lean_object* v_t_516_, lean_object* v_tagged_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_516_, v_tagged_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged_elim(lean_object* v_00_u03c4_519_, lean_object* v_motive_520_, lean_object* v_t_521_, lean_object* v_h_522_, lean_object* v_tagged_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_521_, v_tagged_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim___redArg(lean_object* v_t_525_, lean_object* v_flattened_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_525_, v_flattened_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened_elim(lean_object* v_00_u03c4_528_, lean_object* v_motive_529_, lean_object* v_t_530_, lean_object* v_h_531_, lean_object* v_flattened_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_530_, v_flattened_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim___redArg(lean_object* v_t_534_, lean_object* v_unflattenable_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_534_, v_unflattenable_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable_elim(lean_object* v_00_u03c4_537_, lean_object* v_motive_538_, lean_object* v_t_539_, lean_object* v_h_540_, lean_object* v_unflattenable_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_539_, v_unflattenable_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim___redArg(lean_object* v_t_543_, lean_object* v_indented_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_543_, v_indented_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented_elim(lean_object* v_00_u03c4_546_, lean_object* v_motive_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_indented_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_548_, v_indented_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim___redArg(lean_object* v_t_552_, lean_object* v_aligned_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_552_, v_aligned_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned_elim(lean_object* v_00_u03c4_555_, lean_object* v_motive_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_aligned_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_557_, v_aligned_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim___redArg(lean_object* v_t_561_, lean_object* v_unindented_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_561_, v_unindented_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented_elim(lean_object* v_00_u03c4_564_, lean_object* v_motive_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_unindented_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_566_, v_unindented_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full_elim___redArg(lean_object* v_t_570_, lean_object* v_full_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_570_, v_full_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full_elim(lean_object* v_00_u03c4_573_, lean_object* v_motive_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_full_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_575_, v_full_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim___redArg(lean_object* v_t_579_, lean_object* v_free_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_579_, v_free_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free_elim(lean_object* v_00_u03c4_582_, lean_object* v_motive_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_free_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_584_, v_free_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim___redArg(lean_object* v_t_588_, lean_object* v_guarded_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_588_, v_guarded_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded_elim(lean_object* v_00_u03c4_591_, lean_object* v_motive_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_guarded_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_593_, v_guarded_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim___redArg(lean_object* v_t_597_, lean_object* v_costing_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_597_, v_costing_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing_elim(lean_object* v_00_u03c4_600_, lean_object* v_motive_601_, lean_object* v_t_602_, lean_object* v_h_603_, lean_object* v_costing_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_602_, v_costing_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim___redArg(lean_object* v_t_606_, lean_object* v_either_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_606_, v_either_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either_elim(lean_object* v_00_u03c4_609_, lean_object* v_motive_610_, lean_object* v_t_611_, lean_object* v_h_612_, lean_object* v_either_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_611_, v_either_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim___redArg(lean_object* v_t_615_, lean_object* v_append_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_615_, v_append_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append_elim(lean_object* v_00_u03c4_618_, lean_object* v_motive_619_, lean_object* v_t_620_, lean_object* v_h_621_, lean_object* v_append_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Fmt_Doc_ctorElim___redArg(v_t_620_, v_append_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___redArg(lean_object* v_x_624_, lean_object* v_h__1_625_, lean_object* v_h__2_626_, lean_object* v_h__3_627_, lean_object* v_h__4_628_, lean_object* v_h__5_629_, lean_object* v_h__6_630_, lean_object* v_h__7_631_, lean_object* v_h__8_632_, lean_object* v_h__9_633_, lean_object* v_h__10_634_, lean_object* v_h__11_635_, lean_object* v_h__12_636_, lean_object* v_h__13_637_, lean_object* v_h__14_638_, lean_object* v_h__15_639_){
_start:
{
switch(lean_obj_tag(v_x_624_))
{
case 0:
{
lean_object* v___x_640_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
v___x_640_ = lean_apply_1(v_h__1_625_, lean_box(0));
return v___x_640_;
}
case 1:
{
lean_object* v_f_641_; lean_object* v___x_642_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__1_625_);
v_f_641_ = lean_ctor_get(v_x_624_, 0);
lean_inc_ref(v_f_641_);
lean_dec_ref_known(v_x_624_, 1);
v___x_642_ = lean_apply_2(v_h__2_626_, lean_box(0), v_f_641_);
return v___x_642_;
}
case 2:
{
lean_object* v_s_643_; lean_object* v___x_644_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_s_643_ = lean_ctor_get(v_x_624_, 0);
lean_inc_ref(v_s_643_);
lean_dec_ref_known(v_x_624_, 1);
v___x_644_ = lean_apply_2(v_h__3_627_, lean_box(0), v_s_643_);
return v___x_644_;
}
case 3:
{
lean_object* v_id_645_; lean_object* v_d_646_; lean_object* v___x_647_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_id_645_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_id_645_);
v_d_646_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_d_646_);
lean_dec_ref_known(v_x_624_, 2);
v___x_647_ = lean_apply_3(v_h__5_629_, lean_box(0), v_id_645_, v_d_646_);
return v___x_647_;
}
case 4:
{
lean_object* v_d_648_; lean_object* v___x_649_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_d_648_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_d_648_);
lean_dec_ref_known(v_x_624_, 1);
v___x_649_ = lean_apply_2(v_h__4_628_, lean_box(0), v_d_648_);
return v___x_649_;
}
case 5:
{
lean_object* v_d_650_; lean_object* v___x_651_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_d_650_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_d_650_);
lean_dec_ref_known(v_x_624_, 1);
v___x_651_ = lean_apply_2(v_h__11_635_, lean_box(0), v_d_650_);
return v___x_651_;
}
case 6:
{
lean_object* v_n_652_; uint8_t v_isCumulative_653_; lean_object* v_d_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_n_652_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_n_652_);
v_isCumulative_653_ = lean_ctor_get_uint8(v_x_624_, sizeof(void*)*2);
v_d_654_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_d_654_);
lean_dec_ref_known(v_x_624_, 2);
v___x_655_ = lean_box(v_isCumulative_653_);
v___x_656_ = lean_apply_4(v_h__6_630_, lean_box(0), v_n_652_, v___x_655_, v_d_654_);
return v___x_656_;
}
case 7:
{
lean_object* v_d_657_; lean_object* v___x_658_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_d_657_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_d_657_);
lean_dec_ref_known(v_x_624_, 1);
v___x_658_ = lean_apply_2(v_h__7_631_, lean_box(0), v_d_657_);
return v___x_658_;
}
case 8:
{
uint8_t v_onlyNonCumulative_659_; lean_object* v_d_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_onlyNonCumulative_659_ = lean_ctor_get_uint8(v_x_624_, sizeof(void*)*1);
v_d_660_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_d_660_);
lean_dec_ref_known(v_x_624_, 1);
v___x_661_ = lean_box(v_onlyNonCumulative_659_);
v___x_662_ = lean_apply_3(v_h__8_632_, lean_box(0), v___x_661_, v_d_660_);
return v___x_662_;
}
case 9:
{
lean_object* v_d_663_; lean_object* v___x_664_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_d_663_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_d_663_);
lean_dec_ref_known(v_x_624_, 1);
v___x_664_ = lean_apply_2(v_h__9_633_, lean_box(0), v_d_663_);
return v___x_664_;
}
case 10:
{
lean_object* v_d_665_; lean_object* v___x_666_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_d_665_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_d_665_);
lean_dec_ref_known(v_x_624_, 1);
v___x_666_ = lean_apply_2(v_h__10_634_, lean_box(0), v_d_665_);
return v___x_666_;
}
case 11:
{
lean_object* v_p_667_; lean_object* v_d_668_; lean_object* v___x_669_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_p_667_ = lean_ctor_get(v_x_624_, 0);
lean_inc_ref(v_p_667_);
v_d_668_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_d_668_);
lean_dec_ref_known(v_x_624_, 2);
v___x_669_ = lean_apply_3(v_h__12_636_, lean_box(0), v_p_667_, v_d_668_);
return v___x_669_;
}
case 12:
{
lean_object* v_cost_670_; lean_object* v_d_671_; lean_object* v___x_672_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__14_638_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_cost_670_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_cost_670_);
v_d_671_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_d_671_);
lean_dec_ref_known(v_x_624_, 2);
v___x_672_ = lean_apply_3(v_h__13_637_, lean_box(0), v_cost_670_, v_d_671_);
return v___x_672_;
}
case 13:
{
lean_object* v_a_673_; lean_object* v_b_674_; lean_object* v___x_675_; 
lean_dec(v_h__15_639_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_a_673_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_a_673_);
v_b_674_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_b_674_);
lean_dec_ref_known(v_x_624_, 2);
v___x_675_ = lean_apply_3(v_h__14_638_, lean_box(0), v_a_673_, v_b_674_);
return v___x_675_;
}
default: 
{
lean_object* v_a_676_; lean_object* v_b_677_; lean_object* v___x_678_; 
lean_dec(v_h__14_638_);
lean_dec(v_h__13_637_);
lean_dec(v_h__12_636_);
lean_dec(v_h__11_635_);
lean_dec(v_h__10_634_);
lean_dec(v_h__9_633_);
lean_dec(v_h__8_632_);
lean_dec(v_h__7_631_);
lean_dec(v_h__6_630_);
lean_dec(v_h__5_629_);
lean_dec(v_h__4_628_);
lean_dec(v_h__3_627_);
lean_dec(v_h__2_626_);
lean_dec(v_h__1_625_);
v_a_676_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_a_676_);
v_b_677_ = lean_ctor_get(v_x_624_, 1);
lean_inc(v_b_677_);
lean_dec_ref_known(v_x_624_, 2);
v___x_678_ = lean_apply_3(v_h__15_639_, lean_box(0), v_a_676_, v_b_677_);
return v___x_678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(lean_object* v_motive_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_h__1_682_, lean_object* v_h__2_683_, lean_object* v_h__3_684_, lean_object* v_h__4_685_, lean_object* v_h__5_686_, lean_object* v_h__6_687_, lean_object* v_h__7_688_, lean_object* v_h__8_689_, lean_object* v_h__9_690_, lean_object* v_h__10_691_, lean_object* v_h__11_692_, lean_object* v_h__12_693_, lean_object* v_h__13_694_, lean_object* v_h__14_695_, lean_object* v_h__15_696_){
_start:
{
switch(lean_obj_tag(v_x_681_))
{
case 0:
{
lean_object* v___x_697_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
v___x_697_ = lean_apply_1(v_h__1_682_, lean_box(0));
return v___x_697_;
}
case 1:
{
lean_object* v_f_698_; lean_object* v___x_699_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__1_682_);
v_f_698_ = lean_ctor_get(v_x_681_, 0);
lean_inc_ref(v_f_698_);
lean_dec_ref_known(v_x_681_, 1);
v___x_699_ = lean_apply_2(v_h__2_683_, lean_box(0), v_f_698_);
return v___x_699_;
}
case 2:
{
lean_object* v_s_700_; lean_object* v___x_701_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_s_700_ = lean_ctor_get(v_x_681_, 0);
lean_inc_ref(v_s_700_);
lean_dec_ref_known(v_x_681_, 1);
v___x_701_ = lean_apply_2(v_h__3_684_, lean_box(0), v_s_700_);
return v___x_701_;
}
case 3:
{
lean_object* v_id_702_; lean_object* v_d_703_; lean_object* v___x_704_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_id_702_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_id_702_);
v_d_703_ = lean_ctor_get(v_x_681_, 1);
lean_inc(v_d_703_);
lean_dec_ref_known(v_x_681_, 2);
v___x_704_ = lean_apply_3(v_h__5_686_, lean_box(0), v_id_702_, v_d_703_);
return v___x_704_;
}
case 4:
{
lean_object* v_d_705_; lean_object* v___x_706_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_d_705_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_d_705_);
lean_dec_ref_known(v_x_681_, 1);
v___x_706_ = lean_apply_2(v_h__4_685_, lean_box(0), v_d_705_);
return v___x_706_;
}
case 5:
{
lean_object* v_d_707_; lean_object* v___x_708_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_d_707_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_d_707_);
lean_dec_ref_known(v_x_681_, 1);
v___x_708_ = lean_apply_2(v_h__11_692_, lean_box(0), v_d_707_);
return v___x_708_;
}
case 6:
{
lean_object* v_n_709_; uint8_t v_isCumulative_710_; lean_object* v_d_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_n_709_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_n_709_);
v_isCumulative_710_ = lean_ctor_get_uint8(v_x_681_, sizeof(void*)*2);
v_d_711_ = lean_ctor_get(v_x_681_, 1);
lean_inc(v_d_711_);
lean_dec_ref_known(v_x_681_, 2);
v___x_712_ = lean_box(v_isCumulative_710_);
v___x_713_ = lean_apply_4(v_h__6_687_, lean_box(0), v_n_709_, v___x_712_, v_d_711_);
return v___x_713_;
}
case 7:
{
lean_object* v_d_714_; lean_object* v___x_715_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_d_714_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_d_714_);
lean_dec_ref_known(v_x_681_, 1);
v___x_715_ = lean_apply_2(v_h__7_688_, lean_box(0), v_d_714_);
return v___x_715_;
}
case 8:
{
uint8_t v_onlyNonCumulative_716_; lean_object* v_d_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_onlyNonCumulative_716_ = lean_ctor_get_uint8(v_x_681_, sizeof(void*)*1);
v_d_717_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_d_717_);
lean_dec_ref_known(v_x_681_, 1);
v___x_718_ = lean_box(v_onlyNonCumulative_716_);
v___x_719_ = lean_apply_3(v_h__8_689_, lean_box(0), v___x_718_, v_d_717_);
return v___x_719_;
}
case 9:
{
lean_object* v_d_720_; lean_object* v___x_721_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_d_720_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_d_720_);
lean_dec_ref_known(v_x_681_, 1);
v___x_721_ = lean_apply_2(v_h__9_690_, lean_box(0), v_d_720_);
return v___x_721_;
}
case 10:
{
lean_object* v_d_722_; lean_object* v___x_723_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_d_722_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_d_722_);
lean_dec_ref_known(v_x_681_, 1);
v___x_723_ = lean_apply_2(v_h__10_691_, lean_box(0), v_d_722_);
return v___x_723_;
}
case 11:
{
lean_object* v_p_724_; lean_object* v_d_725_; lean_object* v___x_726_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_p_724_ = lean_ctor_get(v_x_681_, 0);
lean_inc_ref(v_p_724_);
v_d_725_ = lean_ctor_get(v_x_681_, 1);
lean_inc(v_d_725_);
lean_dec_ref_known(v_x_681_, 2);
v___x_726_ = lean_apply_3(v_h__12_693_, lean_box(0), v_p_724_, v_d_725_);
return v___x_726_;
}
case 12:
{
lean_object* v_cost_727_; lean_object* v_d_728_; lean_object* v___x_729_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__14_695_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_cost_727_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_cost_727_);
v_d_728_ = lean_ctor_get(v_x_681_, 1);
lean_inc(v_d_728_);
lean_dec_ref_known(v_x_681_, 2);
v___x_729_ = lean_apply_3(v_h__13_694_, lean_box(0), v_cost_727_, v_d_728_);
return v___x_729_;
}
case 13:
{
lean_object* v_a_730_; lean_object* v_b_731_; lean_object* v___x_732_; 
lean_dec(v_h__15_696_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_a_730_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_a_730_);
v_b_731_ = lean_ctor_get(v_x_681_, 1);
lean_inc(v_b_731_);
lean_dec_ref_known(v_x_681_, 2);
v___x_732_ = lean_apply_3(v_h__14_695_, lean_box(0), v_a_730_, v_b_731_);
return v___x_732_;
}
default: 
{
lean_object* v_a_733_; lean_object* v_b_734_; lean_object* v___x_735_; 
lean_dec(v_h__14_695_);
lean_dec(v_h__13_694_);
lean_dec(v_h__12_693_);
lean_dec(v_h__11_692_);
lean_dec(v_h__10_691_);
lean_dec(v_h__9_690_);
lean_dec(v_h__8_689_);
lean_dec(v_h__7_688_);
lean_dec(v_h__6_687_);
lean_dec(v_h__5_686_);
lean_dec(v_h__4_685_);
lean_dec(v_h__3_684_);
lean_dec(v_h__2_683_);
lean_dec(v_h__1_682_);
v_a_733_ = lean_ctor_get(v_x_681_, 0);
lean_inc(v_a_733_);
v_b_734_ = lean_ctor_get(v_x_681_, 1);
lean_inc(v_b_734_);
lean_dec_ref_known(v_x_681_, 2);
v___x_735_ = lean_apply_3(v_h__15_696_, lean_box(0), v_a_733_, v_b_734_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter___boxed(lean_object** _args){
lean_object* v_motive_736_ = _args[0];
lean_object* v_x_737_ = _args[1];
lean_object* v_x_738_ = _args[2];
lean_object* v_h__1_739_ = _args[3];
lean_object* v_h__2_740_ = _args[4];
lean_object* v_h__3_741_ = _args[5];
lean_object* v_h__4_742_ = _args[6];
lean_object* v_h__5_743_ = _args[7];
lean_object* v_h__6_744_ = _args[8];
lean_object* v_h__7_745_ = _args[9];
lean_object* v_h__8_746_ = _args[10];
lean_object* v_h__9_747_ = _args[11];
lean_object* v_h__10_748_ = _args[12];
lean_object* v_h__11_749_ = _args[13];
lean_object* v_h__12_750_ = _args[14];
lean_object* v_h__13_751_ = _args[15];
lean_object* v_h__14_752_ = _args[16];
lean_object* v_h__15_753_ = _args[17];
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_maxNewlineCount_x3f_match__1_splitter(v_motive_736_, v_x_737_, v_x_738_, v_h__1_739_, v_h__2_740_, v_h__3_741_, v_h__4_742_, v_h__5_743_, v_h__6_744_, v_h__7_745_, v_h__8_746_, v_h__9_747_, v_h__10_748_, v_h__11_749_, v_h__12_750_, v_h__13_751_, v_h__14_752_, v_h__15_753_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___redArg(lean_object* v_x_755_, lean_object* v_h__1_756_, lean_object* v_h__2_757_, lean_object* v_h__3_758_, lean_object* v_h__4_759_, lean_object* v_h__5_760_, lean_object* v_h__6_761_, lean_object* v_h__7_762_, lean_object* v_h__8_763_, lean_object* v_h__9_764_, lean_object* v_h__10_765_, lean_object* v_h__11_766_, lean_object* v_h__12_767_, lean_object* v_h__13_768_, lean_object* v_h__14_769_, lean_object* v_h__15_770_){
_start:
{
switch(lean_obj_tag(v_x_755_))
{
case 0:
{
lean_object* v___x_771_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
v___x_771_ = lean_apply_1(v_h__1_756_, lean_box(0));
return v___x_771_;
}
case 1:
{
lean_object* v_f_772_; lean_object* v___x_773_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__1_756_);
v_f_772_ = lean_ctor_get(v_x_755_, 0);
lean_inc_ref(v_f_772_);
lean_dec_ref_known(v_x_755_, 1);
v___x_773_ = lean_apply_2(v_h__2_757_, lean_box(0), v_f_772_);
return v___x_773_;
}
case 2:
{
lean_object* v_s_774_; lean_object* v___x_775_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_s_774_ = lean_ctor_get(v_x_755_, 0);
lean_inc_ref(v_s_774_);
lean_dec_ref_known(v_x_755_, 1);
v___x_775_ = lean_apply_2(v_h__3_758_, lean_box(0), v_s_774_);
return v___x_775_;
}
case 3:
{
lean_object* v_id_776_; lean_object* v_d_777_; lean_object* v___x_778_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_id_776_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_id_776_);
v_d_777_ = lean_ctor_get(v_x_755_, 1);
lean_inc(v_d_777_);
lean_dec_ref_known(v_x_755_, 2);
v___x_778_ = lean_apply_3(v_h__6_761_, lean_box(0), v_id_776_, v_d_777_);
return v___x_778_;
}
case 4:
{
lean_object* v_d_779_; lean_object* v___x_780_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_d_779_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_d_779_);
lean_dec_ref_known(v_x_755_, 1);
v___x_780_ = lean_apply_2(v_h__4_759_, lean_box(0), v_d_779_);
return v___x_780_;
}
case 5:
{
lean_object* v_d_781_; lean_object* v___x_782_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_d_781_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_d_781_);
lean_dec_ref_known(v_x_755_, 1);
v___x_782_ = lean_apply_2(v_h__5_760_, lean_box(0), v_d_781_);
return v___x_782_;
}
case 6:
{
lean_object* v_n_783_; uint8_t v_isCumulative_784_; lean_object* v_d_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_n_783_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_n_783_);
v_isCumulative_784_ = lean_ctor_get_uint8(v_x_755_, sizeof(void*)*2);
v_d_785_ = lean_ctor_get(v_x_755_, 1);
lean_inc(v_d_785_);
lean_dec_ref_known(v_x_755_, 2);
v___x_786_ = lean_box(v_isCumulative_784_);
v___x_787_ = lean_apply_4(v_h__7_762_, lean_box(0), v_n_783_, v___x_786_, v_d_785_);
return v___x_787_;
}
case 7:
{
lean_object* v_d_788_; lean_object* v___x_789_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_d_788_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_d_788_);
lean_dec_ref_known(v_x_755_, 1);
v___x_789_ = lean_apply_2(v_h__8_763_, lean_box(0), v_d_788_);
return v___x_789_;
}
case 8:
{
uint8_t v_onlyNonCumulative_790_; lean_object* v_d_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_onlyNonCumulative_790_ = lean_ctor_get_uint8(v_x_755_, sizeof(void*)*1);
v_d_791_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_d_791_);
lean_dec_ref_known(v_x_755_, 1);
v___x_792_ = lean_box(v_onlyNonCumulative_790_);
v___x_793_ = lean_apply_3(v_h__9_764_, lean_box(0), v___x_792_, v_d_791_);
return v___x_793_;
}
case 9:
{
lean_object* v_d_794_; lean_object* v___x_795_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_d_794_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_d_794_);
lean_dec_ref_known(v_x_755_, 1);
v___x_795_ = lean_apply_2(v_h__10_765_, lean_box(0), v_d_794_);
return v___x_795_;
}
case 10:
{
lean_object* v_d_796_; lean_object* v___x_797_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_d_796_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_d_796_);
lean_dec_ref_known(v_x_755_, 1);
v___x_797_ = lean_apply_2(v_h__11_766_, lean_box(0), v_d_796_);
return v___x_797_;
}
case 11:
{
lean_object* v_p_798_; lean_object* v_d_799_; lean_object* v___x_800_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_p_798_ = lean_ctor_get(v_x_755_, 0);
lean_inc_ref(v_p_798_);
v_d_799_ = lean_ctor_get(v_x_755_, 1);
lean_inc(v_d_799_);
lean_dec_ref_known(v_x_755_, 2);
v___x_800_ = lean_apply_3(v_h__12_767_, lean_box(0), v_p_798_, v_d_799_);
return v___x_800_;
}
case 12:
{
lean_object* v_cost_801_; lean_object* v_d_802_; lean_object* v___x_803_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__14_769_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_cost_801_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_cost_801_);
v_d_802_ = lean_ctor_get(v_x_755_, 1);
lean_inc(v_d_802_);
lean_dec_ref_known(v_x_755_, 2);
v___x_803_ = lean_apply_3(v_h__13_768_, lean_box(0), v_cost_801_, v_d_802_);
return v___x_803_;
}
case 13:
{
lean_object* v_a_804_; lean_object* v_b_805_; lean_object* v___x_806_; 
lean_dec(v_h__15_770_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_a_804_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_a_804_);
v_b_805_ = lean_ctor_get(v_x_755_, 1);
lean_inc(v_b_805_);
lean_dec_ref_known(v_x_755_, 2);
v___x_806_ = lean_apply_3(v_h__14_769_, lean_box(0), v_a_804_, v_b_805_);
return v___x_806_;
}
default: 
{
lean_object* v_a_807_; lean_object* v_b_808_; lean_object* v___x_809_; 
lean_dec(v_h__14_769_);
lean_dec(v_h__13_768_);
lean_dec(v_h__12_767_);
lean_dec(v_h__11_766_);
lean_dec(v_h__10_765_);
lean_dec(v_h__9_764_);
lean_dec(v_h__8_763_);
lean_dec(v_h__7_762_);
lean_dec(v_h__6_761_);
lean_dec(v_h__5_760_);
lean_dec(v_h__4_759_);
lean_dec(v_h__3_758_);
lean_dec(v_h__2_757_);
lean_dec(v_h__1_756_);
v_a_807_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_a_807_);
v_b_808_ = lean_ctor_get(v_x_755_, 1);
lean_inc(v_b_808_);
lean_dec_ref_known(v_x_755_, 2);
v___x_809_ = lean_apply_3(v_h__15_770_, lean_box(0), v_a_807_, v_b_808_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(lean_object* v_motive_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_h__1_813_, lean_object* v_h__2_814_, lean_object* v_h__3_815_, lean_object* v_h__4_816_, lean_object* v_h__5_817_, lean_object* v_h__6_818_, lean_object* v_h__7_819_, lean_object* v_h__8_820_, lean_object* v_h__9_821_, lean_object* v_h__10_822_, lean_object* v_h__11_823_, lean_object* v_h__12_824_, lean_object* v_h__13_825_, lean_object* v_h__14_826_, lean_object* v_h__15_827_){
_start:
{
switch(lean_obj_tag(v_x_812_))
{
case 0:
{
lean_object* v___x_828_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
v___x_828_ = lean_apply_1(v_h__1_813_, lean_box(0));
return v___x_828_;
}
case 1:
{
lean_object* v_f_829_; lean_object* v___x_830_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__1_813_);
v_f_829_ = lean_ctor_get(v_x_812_, 0);
lean_inc_ref(v_f_829_);
lean_dec_ref_known(v_x_812_, 1);
v___x_830_ = lean_apply_2(v_h__2_814_, lean_box(0), v_f_829_);
return v___x_830_;
}
case 2:
{
lean_object* v_s_831_; lean_object* v___x_832_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_s_831_ = lean_ctor_get(v_x_812_, 0);
lean_inc_ref(v_s_831_);
lean_dec_ref_known(v_x_812_, 1);
v___x_832_ = lean_apply_2(v_h__3_815_, lean_box(0), v_s_831_);
return v___x_832_;
}
case 3:
{
lean_object* v_id_833_; lean_object* v_d_834_; lean_object* v___x_835_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_id_833_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_id_833_);
v_d_834_ = lean_ctor_get(v_x_812_, 1);
lean_inc(v_d_834_);
lean_dec_ref_known(v_x_812_, 2);
v___x_835_ = lean_apply_3(v_h__6_818_, lean_box(0), v_id_833_, v_d_834_);
return v___x_835_;
}
case 4:
{
lean_object* v_d_836_; lean_object* v___x_837_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_d_836_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_d_836_);
lean_dec_ref_known(v_x_812_, 1);
v___x_837_ = lean_apply_2(v_h__4_816_, lean_box(0), v_d_836_);
return v___x_837_;
}
case 5:
{
lean_object* v_d_838_; lean_object* v___x_839_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_d_838_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_d_838_);
lean_dec_ref_known(v_x_812_, 1);
v___x_839_ = lean_apply_2(v_h__5_817_, lean_box(0), v_d_838_);
return v___x_839_;
}
case 6:
{
lean_object* v_n_840_; uint8_t v_isCumulative_841_; lean_object* v_d_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_n_840_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_n_840_);
v_isCumulative_841_ = lean_ctor_get_uint8(v_x_812_, sizeof(void*)*2);
v_d_842_ = lean_ctor_get(v_x_812_, 1);
lean_inc(v_d_842_);
lean_dec_ref_known(v_x_812_, 2);
v___x_843_ = lean_box(v_isCumulative_841_);
v___x_844_ = lean_apply_4(v_h__7_819_, lean_box(0), v_n_840_, v___x_843_, v_d_842_);
return v___x_844_;
}
case 7:
{
lean_object* v_d_845_; lean_object* v___x_846_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_d_845_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_d_845_);
lean_dec_ref_known(v_x_812_, 1);
v___x_846_ = lean_apply_2(v_h__8_820_, lean_box(0), v_d_845_);
return v___x_846_;
}
case 8:
{
uint8_t v_onlyNonCumulative_847_; lean_object* v_d_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_onlyNonCumulative_847_ = lean_ctor_get_uint8(v_x_812_, sizeof(void*)*1);
v_d_848_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_d_848_);
lean_dec_ref_known(v_x_812_, 1);
v___x_849_ = lean_box(v_onlyNonCumulative_847_);
v___x_850_ = lean_apply_3(v_h__9_821_, lean_box(0), v___x_849_, v_d_848_);
return v___x_850_;
}
case 9:
{
lean_object* v_d_851_; lean_object* v___x_852_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_d_851_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_d_851_);
lean_dec_ref_known(v_x_812_, 1);
v___x_852_ = lean_apply_2(v_h__10_822_, lean_box(0), v_d_851_);
return v___x_852_;
}
case 10:
{
lean_object* v_d_853_; lean_object* v___x_854_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_d_853_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_d_853_);
lean_dec_ref_known(v_x_812_, 1);
v___x_854_ = lean_apply_2(v_h__11_823_, lean_box(0), v_d_853_);
return v___x_854_;
}
case 11:
{
lean_object* v_p_855_; lean_object* v_d_856_; lean_object* v___x_857_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_p_855_ = lean_ctor_get(v_x_812_, 0);
lean_inc_ref(v_p_855_);
v_d_856_ = lean_ctor_get(v_x_812_, 1);
lean_inc(v_d_856_);
lean_dec_ref_known(v_x_812_, 2);
v___x_857_ = lean_apply_3(v_h__12_824_, lean_box(0), v_p_855_, v_d_856_);
return v___x_857_;
}
case 12:
{
lean_object* v_cost_858_; lean_object* v_d_859_; lean_object* v___x_860_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__14_826_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_cost_858_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_cost_858_);
v_d_859_ = lean_ctor_get(v_x_812_, 1);
lean_inc(v_d_859_);
lean_dec_ref_known(v_x_812_, 2);
v___x_860_ = lean_apply_3(v_h__13_825_, lean_box(0), v_cost_858_, v_d_859_);
return v___x_860_;
}
case 13:
{
lean_object* v_a_861_; lean_object* v_b_862_; lean_object* v___x_863_; 
lean_dec(v_h__15_827_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_a_861_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_a_861_);
v_b_862_ = lean_ctor_get(v_x_812_, 1);
lean_inc(v_b_862_);
lean_dec_ref_known(v_x_812_, 2);
v___x_863_ = lean_apply_3(v_h__14_826_, lean_box(0), v_a_861_, v_b_862_);
return v___x_863_;
}
default: 
{
lean_object* v_a_864_; lean_object* v_b_865_; lean_object* v___x_866_; 
lean_dec(v_h__14_826_);
lean_dec(v_h__13_825_);
lean_dec(v_h__12_824_);
lean_dec(v_h__11_823_);
lean_dec(v_h__10_822_);
lean_dec(v_h__9_821_);
lean_dec(v_h__8_820_);
lean_dec(v_h__7_819_);
lean_dec(v_h__6_818_);
lean_dec(v_h__5_817_);
lean_dec(v_h__4_816_);
lean_dec(v_h__3_815_);
lean_dec(v_h__2_814_);
lean_dec(v_h__1_813_);
v_a_864_ = lean_ctor_get(v_x_812_, 0);
lean_inc(v_a_864_);
v_b_865_ = lean_ctor_get(v_x_812_, 1);
lean_inc(v_b_865_);
lean_dec_ref_known(v_x_812_, 2);
v___x_866_ = lean_apply_3(v_h__15_827_, lean_box(0), v_a_864_, v_b_865_);
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter___boxed(lean_object** _args){
lean_object* v_motive_867_ = _args[0];
lean_object* v_x_868_ = _args[1];
lean_object* v_x_869_ = _args[2];
lean_object* v_h__1_870_ = _args[3];
lean_object* v_h__2_871_ = _args[4];
lean_object* v_h__3_872_ = _args[5];
lean_object* v_h__4_873_ = _args[6];
lean_object* v_h__5_874_ = _args[7];
lean_object* v_h__6_875_ = _args[8];
lean_object* v_h__7_876_ = _args[9];
lean_object* v_h__8_877_ = _args[10];
lean_object* v_h__9_878_ = _args[11];
lean_object* v_h__10_879_ = _args[12];
lean_object* v_h__11_880_ = _args[13];
lean_object* v_h__12_881_ = _args[14];
lean_object* v_h__13_882_ = _args[15];
lean_object* v_h__14_883_ = _args[16];
lean_object* v_h__15_884_ = _args[17];
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__2_splitter(v_motive_867_, v_x_868_, v_x_869_, v_h__1_870_, v_h__2_871_, v_h__3_872_, v_h__4_873_, v_h__5_874_, v_h__6_875_, v_h__7_876_, v_h__8_877_, v_h__9_878_, v_h__10_879_, v_h__11_880_, v_h__12_881_, v_h__13_882_, v_h__14_883_, v_h__15_884_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(uint8_t v_x_886_, lean_object* v_h__1_887_, lean_object* v_h__2_888_, lean_object* v_h__3_889_){
_start:
{
switch(v_x_886_)
{
case 0:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec(v_h__3_889_);
lean_dec(v_h__2_888_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_apply_1(v_h__1_887_, v___x_890_);
return v___x_891_;
}
case 1:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec(v_h__3_889_);
lean_dec(v_h__1_887_);
v___x_892_ = lean_box(0);
v___x_893_ = lean_apply_1(v_h__2_888_, v___x_892_);
return v___x_893_;
}
default: 
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v_h__2_888_);
lean_dec(v_h__1_887_);
v___x_894_ = lean_box(0);
v___x_895_ = lean_apply_1(v_h__3_889_, v___x_894_);
return v___x_895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg___boxed(lean_object* v_x_896_, lean_object* v_h__1_897_, lean_object* v_h__2_898_, lean_object* v_h__3_899_){
_start:
{
uint8_t v_x_33__boxed_900_; lean_object* v_res_901_; 
v_x_33__boxed_900_ = lean_unbox(v_x_896_);
v_res_901_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___redArg(v_x_33__boxed_900_, v_h__1_897_, v_h__2_898_, v_h__3_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(lean_object* v_motive_902_, uint8_t v_x_903_, lean_object* v_h__1_904_, lean_object* v_h__2_905_, lean_object* v_h__3_906_){
_start:
{
switch(v_x_903_)
{
case 0:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_dec(v_h__3_906_);
lean_dec(v_h__2_905_);
v___x_907_ = lean_box(0);
v___x_908_ = lean_apply_1(v_h__1_904_, v___x_907_);
return v___x_908_;
}
case 1:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_h__3_906_);
lean_dec(v_h__1_904_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_apply_1(v_h__2_905_, v___x_909_);
return v___x_910_;
}
default: 
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec(v_h__2_905_);
lean_dec(v_h__1_904_);
v___x_911_ = lean_box(0);
v___x_912_ = lean_apply_1(v_h__3_906_, v___x_911_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter___boxed(lean_object* v_motive_913_, lean_object* v_x_914_, lean_object* v_h__1_915_, lean_object* v_h__2_916_, lean_object* v_h__3_917_){
_start:
{
uint8_t v_x_48__boxed_918_; lean_object* v_res_919_; 
v_x_48__boxed_918_ = lean_unbox(v_x_914_);
v_res_919_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_alwaysEmptiness_match__1_splitter(v_motive_913_, v_x_48__boxed_918_, v_h__1_915_, v_h__2_916_, v_h__3_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___redArg(lean_object* v_x_920_, lean_object* v_h__1_921_, lean_object* v_h__2_922_, lean_object* v_h__3_923_, lean_object* v_h__4_924_, lean_object* v_h__5_925_, lean_object* v_h__6_926_, lean_object* v_h__7_927_, lean_object* v_h__8_928_, lean_object* v_h__9_929_, lean_object* v_h__10_930_, lean_object* v_h__11_931_, lean_object* v_h__12_932_, lean_object* v_h__13_933_, lean_object* v_h__14_934_, lean_object* v_h__15_935_){
_start:
{
switch(lean_obj_tag(v_x_920_))
{
case 0:
{
lean_object* v___x_936_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
v___x_936_ = lean_apply_1(v_h__1_921_, lean_box(0));
return v___x_936_;
}
case 1:
{
lean_object* v_f_937_; lean_object* v___x_938_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_f_937_ = lean_ctor_get(v_x_920_, 0);
lean_inc_ref(v_f_937_);
lean_dec_ref_known(v_x_920_, 1);
v___x_938_ = lean_apply_2(v_h__3_923_, lean_box(0), v_f_937_);
return v___x_938_;
}
case 2:
{
lean_object* v_s_939_; lean_object* v___x_940_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__1_921_);
v_s_939_ = lean_ctor_get(v_x_920_, 0);
lean_inc_ref(v_s_939_);
lean_dec_ref_known(v_x_920_, 1);
v___x_940_ = lean_apply_2(v_h__2_922_, lean_box(0), v_s_939_);
return v___x_940_;
}
case 3:
{
lean_object* v_id_941_; lean_object* v_d_942_; lean_object* v___x_943_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_id_941_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_id_941_);
v_d_942_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_d_942_);
lean_dec_ref_known(v_x_920_, 2);
v___x_943_ = lean_apply_3(v_h__6_926_, lean_box(0), v_id_941_, v_d_942_);
return v___x_943_;
}
case 4:
{
lean_object* v_d_944_; lean_object* v___x_945_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_d_944_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_d_944_);
lean_dec_ref_known(v_x_920_, 1);
v___x_945_ = lean_apply_2(v_h__4_924_, lean_box(0), v_d_944_);
return v___x_945_;
}
case 5:
{
lean_object* v_d_946_; lean_object* v___x_947_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_d_946_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_d_946_);
lean_dec_ref_known(v_x_920_, 1);
v___x_947_ = lean_apply_2(v_h__5_925_, lean_box(0), v_d_946_);
return v___x_947_;
}
case 6:
{
lean_object* v_n_948_; uint8_t v_isCumulative_949_; lean_object* v_d_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_n_948_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_n_948_);
v_isCumulative_949_ = lean_ctor_get_uint8(v_x_920_, sizeof(void*)*2);
v_d_950_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_d_950_);
lean_dec_ref_known(v_x_920_, 2);
v___x_951_ = lean_box(v_isCumulative_949_);
v___x_952_ = lean_apply_4(v_h__7_927_, lean_box(0), v_n_948_, v___x_951_, v_d_950_);
return v___x_952_;
}
case 7:
{
lean_object* v_d_953_; lean_object* v___x_954_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_d_953_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_d_953_);
lean_dec_ref_known(v_x_920_, 1);
v___x_954_ = lean_apply_2(v_h__8_928_, lean_box(0), v_d_953_);
return v___x_954_;
}
case 8:
{
uint8_t v_onlyNonCumulative_955_; lean_object* v_d_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_onlyNonCumulative_955_ = lean_ctor_get_uint8(v_x_920_, sizeof(void*)*1);
v_d_956_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_d_956_);
lean_dec_ref_known(v_x_920_, 1);
v___x_957_ = lean_box(v_onlyNonCumulative_955_);
v___x_958_ = lean_apply_3(v_h__9_929_, lean_box(0), v___x_957_, v_d_956_);
return v___x_958_;
}
case 9:
{
lean_object* v_d_959_; lean_object* v___x_960_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_d_959_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_d_959_);
lean_dec_ref_known(v_x_920_, 1);
v___x_960_ = lean_apply_2(v_h__10_930_, lean_box(0), v_d_959_);
return v___x_960_;
}
case 10:
{
lean_object* v_d_961_; lean_object* v___x_962_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_d_961_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_d_961_);
lean_dec_ref_known(v_x_920_, 1);
v___x_962_ = lean_apply_2(v_h__11_931_, lean_box(0), v_d_961_);
return v___x_962_;
}
case 11:
{
lean_object* v_p_963_; lean_object* v_d_964_; lean_object* v___x_965_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_p_963_ = lean_ctor_get(v_x_920_, 0);
lean_inc_ref(v_p_963_);
v_d_964_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_d_964_);
lean_dec_ref_known(v_x_920_, 2);
v___x_965_ = lean_apply_3(v_h__12_932_, lean_box(0), v_p_963_, v_d_964_);
return v___x_965_;
}
case 12:
{
lean_object* v_cost_966_; lean_object* v_d_967_; lean_object* v___x_968_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__14_934_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_cost_966_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_cost_966_);
v_d_967_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_d_967_);
lean_dec_ref_known(v_x_920_, 2);
v___x_968_ = lean_apply_3(v_h__13_933_, lean_box(0), v_cost_966_, v_d_967_);
return v___x_968_;
}
case 13:
{
lean_object* v_a_969_; lean_object* v_b_970_; lean_object* v___x_971_; 
lean_dec(v_h__15_935_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_a_969_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_a_969_);
v_b_970_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_b_970_);
lean_dec_ref_known(v_x_920_, 2);
v___x_971_ = lean_apply_3(v_h__14_934_, lean_box(0), v_a_969_, v_b_970_);
return v___x_971_;
}
default: 
{
lean_object* v_a_972_; lean_object* v_b_973_; lean_object* v___x_974_; 
lean_dec(v_h__14_934_);
lean_dec(v_h__13_933_);
lean_dec(v_h__12_932_);
lean_dec(v_h__11_931_);
lean_dec(v_h__10_930_);
lean_dec(v_h__9_929_);
lean_dec(v_h__8_928_);
lean_dec(v_h__7_927_);
lean_dec(v_h__6_926_);
lean_dec(v_h__5_925_);
lean_dec(v_h__4_924_);
lean_dec(v_h__3_923_);
lean_dec(v_h__2_922_);
lean_dec(v_h__1_921_);
v_a_972_ = lean_ctor_get(v_x_920_, 0);
lean_inc(v_a_972_);
v_b_973_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_b_973_);
lean_dec_ref_known(v_x_920_, 2);
v___x_974_ = lean_apply_3(v_h__15_935_, lean_box(0), v_a_972_, v_b_973_);
return v___x_974_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(lean_object* v_motive_975_, lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_h__1_978_, lean_object* v_h__2_979_, lean_object* v_h__3_980_, lean_object* v_h__4_981_, lean_object* v_h__5_982_, lean_object* v_h__6_983_, lean_object* v_h__7_984_, lean_object* v_h__8_985_, lean_object* v_h__9_986_, lean_object* v_h__10_987_, lean_object* v_h__11_988_, lean_object* v_h__12_989_, lean_object* v_h__13_990_, lean_object* v_h__14_991_, lean_object* v_h__15_992_){
_start:
{
switch(lean_obj_tag(v_x_977_))
{
case 0:
{
lean_object* v___x_993_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
v___x_993_ = lean_apply_1(v_h__1_978_, lean_box(0));
return v___x_993_;
}
case 1:
{
lean_object* v_f_994_; lean_object* v___x_995_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_f_994_ = lean_ctor_get(v_x_977_, 0);
lean_inc_ref(v_f_994_);
lean_dec_ref_known(v_x_977_, 1);
v___x_995_ = lean_apply_2(v_h__3_980_, lean_box(0), v_f_994_);
return v___x_995_;
}
case 2:
{
lean_object* v_s_996_; lean_object* v___x_997_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__1_978_);
v_s_996_ = lean_ctor_get(v_x_977_, 0);
lean_inc_ref(v_s_996_);
lean_dec_ref_known(v_x_977_, 1);
v___x_997_ = lean_apply_2(v_h__2_979_, lean_box(0), v_s_996_);
return v___x_997_;
}
case 3:
{
lean_object* v_id_998_; lean_object* v_d_999_; lean_object* v___x_1000_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_id_998_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_id_998_);
v_d_999_ = lean_ctor_get(v_x_977_, 1);
lean_inc(v_d_999_);
lean_dec_ref_known(v_x_977_, 2);
v___x_1000_ = lean_apply_3(v_h__6_983_, lean_box(0), v_id_998_, v_d_999_);
return v___x_1000_;
}
case 4:
{
lean_object* v_d_1001_; lean_object* v___x_1002_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_d_1001_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_d_1001_);
lean_dec_ref_known(v_x_977_, 1);
v___x_1002_ = lean_apply_2(v_h__4_981_, lean_box(0), v_d_1001_);
return v___x_1002_;
}
case 5:
{
lean_object* v_d_1003_; lean_object* v___x_1004_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_d_1003_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_d_1003_);
lean_dec_ref_known(v_x_977_, 1);
v___x_1004_ = lean_apply_2(v_h__5_982_, lean_box(0), v_d_1003_);
return v___x_1004_;
}
case 6:
{
lean_object* v_n_1005_; uint8_t v_isCumulative_1006_; lean_object* v_d_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_n_1005_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_n_1005_);
v_isCumulative_1006_ = lean_ctor_get_uint8(v_x_977_, sizeof(void*)*2);
v_d_1007_ = lean_ctor_get(v_x_977_, 1);
lean_inc(v_d_1007_);
lean_dec_ref_known(v_x_977_, 2);
v___x_1008_ = lean_box(v_isCumulative_1006_);
v___x_1009_ = lean_apply_4(v_h__7_984_, lean_box(0), v_n_1005_, v___x_1008_, v_d_1007_);
return v___x_1009_;
}
case 7:
{
lean_object* v_d_1010_; lean_object* v___x_1011_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_d_1010_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_d_1010_);
lean_dec_ref_known(v_x_977_, 1);
v___x_1011_ = lean_apply_2(v_h__8_985_, lean_box(0), v_d_1010_);
return v___x_1011_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1012_; lean_object* v_d_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_onlyNonCumulative_1012_ = lean_ctor_get_uint8(v_x_977_, sizeof(void*)*1);
v_d_1013_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_d_1013_);
lean_dec_ref_known(v_x_977_, 1);
v___x_1014_ = lean_box(v_onlyNonCumulative_1012_);
v___x_1015_ = lean_apply_3(v_h__9_986_, lean_box(0), v___x_1014_, v_d_1013_);
return v___x_1015_;
}
case 9:
{
lean_object* v_d_1016_; lean_object* v___x_1017_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_d_1016_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_d_1016_);
lean_dec_ref_known(v_x_977_, 1);
v___x_1017_ = lean_apply_2(v_h__10_987_, lean_box(0), v_d_1016_);
return v___x_1017_;
}
case 10:
{
lean_object* v_d_1018_; lean_object* v___x_1019_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_d_1018_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_d_1018_);
lean_dec_ref_known(v_x_977_, 1);
v___x_1019_ = lean_apply_2(v_h__11_988_, lean_box(0), v_d_1018_);
return v___x_1019_;
}
case 11:
{
lean_object* v_p_1020_; lean_object* v_d_1021_; lean_object* v___x_1022_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_p_1020_ = lean_ctor_get(v_x_977_, 0);
lean_inc_ref(v_p_1020_);
v_d_1021_ = lean_ctor_get(v_x_977_, 1);
lean_inc(v_d_1021_);
lean_dec_ref_known(v_x_977_, 2);
v___x_1022_ = lean_apply_3(v_h__12_989_, lean_box(0), v_p_1020_, v_d_1021_);
return v___x_1022_;
}
case 12:
{
lean_object* v_cost_1023_; lean_object* v_d_1024_; lean_object* v___x_1025_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__14_991_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_cost_1023_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_cost_1023_);
v_d_1024_ = lean_ctor_get(v_x_977_, 1);
lean_inc(v_d_1024_);
lean_dec_ref_known(v_x_977_, 2);
v___x_1025_ = lean_apply_3(v_h__13_990_, lean_box(0), v_cost_1023_, v_d_1024_);
return v___x_1025_;
}
case 13:
{
lean_object* v_a_1026_; lean_object* v_b_1027_; lean_object* v___x_1028_; 
lean_dec(v_h__15_992_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_a_1026_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_a_1026_);
v_b_1027_ = lean_ctor_get(v_x_977_, 1);
lean_inc(v_b_1027_);
lean_dec_ref_known(v_x_977_, 2);
v___x_1028_ = lean_apply_3(v_h__14_991_, lean_box(0), v_a_1026_, v_b_1027_);
return v___x_1028_;
}
default: 
{
lean_object* v_a_1029_; lean_object* v_b_1030_; lean_object* v___x_1031_; 
lean_dec(v_h__14_991_);
lean_dec(v_h__13_990_);
lean_dec(v_h__12_989_);
lean_dec(v_h__11_988_);
lean_dec(v_h__10_987_);
lean_dec(v_h__9_986_);
lean_dec(v_h__8_985_);
lean_dec(v_h__7_984_);
lean_dec(v_h__6_983_);
lean_dec(v_h__5_982_);
lean_dec(v_h__4_981_);
lean_dec(v_h__3_980_);
lean_dec(v_h__2_979_);
lean_dec(v_h__1_978_);
v_a_1029_ = lean_ctor_get(v_x_977_, 0);
lean_inc(v_a_1029_);
v_b_1030_ = lean_ctor_get(v_x_977_, 1);
lean_inc(v_b_1030_);
lean_dec_ref_known(v_x_977_, 2);
v___x_1031_ = lean_apply_3(v_h__15_992_, lean_box(0), v_a_1029_, v_b_1030_);
return v___x_1031_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter___boxed(lean_object** _args){
lean_object* v_motive_1032_ = _args[0];
lean_object* v_x_1033_ = _args[1];
lean_object* v_x_1034_ = _args[2];
lean_object* v_h__1_1035_ = _args[3];
lean_object* v_h__2_1036_ = _args[4];
lean_object* v_h__3_1037_ = _args[5];
lean_object* v_h__4_1038_ = _args[6];
lean_object* v_h__5_1039_ = _args[7];
lean_object* v_h__6_1040_ = _args[8];
lean_object* v_h__7_1041_ = _args[9];
lean_object* v_h__8_1042_ = _args[10];
lean_object* v_h__9_1043_ = _args[11];
lean_object* v_h__10_1044_ = _args[12];
lean_object* v_h__11_1045_ = _args[13];
lean_object* v_h__12_1046_ = _args[14];
lean_object* v_h__13_1047_ = _args[15];
lean_object* v_h__14_1048_ = _args[16];
lean_object* v_h__15_1049_ = _args[17];
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__4_splitter(v_motive_1032_, v_x_1033_, v_x_1034_, v_h__1_1035_, v_h__2_1036_, v_h__3_1037_, v_h__4_1038_, v_h__5_1039_, v_h__6_1040_, v_h__7_1041_, v_h__8_1042_, v_h__9_1043_, v_h__10_1044_, v_h__11_1045_, v_h__12_1046_, v_h__13_1047_, v_h__14_1048_, v_h__15_1049_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(uint8_t v_x_1051_, lean_object* v_h__1_1052_, lean_object* v_h__2_1053_, lean_object* v_h__3_1054_, lean_object* v_h__4_1055_, lean_object* v_h__5_1056_){
_start:
{
switch(v_x_1051_)
{
case 0:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v_h__5_1056_);
lean_dec(v_h__4_1055_);
lean_dec(v_h__3_1054_);
lean_dec(v_h__2_1053_);
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_apply_1(v_h__1_1052_, v___x_1057_);
return v___x_1058_;
}
case 1:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_h__5_1056_);
lean_dec(v_h__4_1055_);
lean_dec(v_h__3_1054_);
lean_dec(v_h__1_1052_);
v___x_1059_ = lean_box(0);
v___x_1060_ = lean_apply_1(v_h__2_1053_, v___x_1059_);
return v___x_1060_;
}
case 2:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
lean_dec(v_h__5_1056_);
lean_dec(v_h__4_1055_);
lean_dec(v_h__2_1053_);
lean_dec(v_h__1_1052_);
v___x_1061_ = lean_box(0);
v___x_1062_ = lean_apply_1(v_h__3_1054_, v___x_1061_);
return v___x_1062_;
}
case 3:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec(v_h__5_1056_);
lean_dec(v_h__3_1054_);
lean_dec(v_h__2_1053_);
lean_dec(v_h__1_1052_);
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_apply_1(v_h__4_1055_, v___x_1063_);
return v___x_1064_;
}
default: 
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec(v_h__4_1055_);
lean_dec(v_h__3_1054_);
lean_dec(v_h__2_1053_);
lean_dec(v_h__1_1052_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_apply_1(v_h__5_1056_, v___x_1065_);
return v___x_1066_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg___boxed(lean_object* v_x_1067_, lean_object* v_h__1_1068_, lean_object* v_h__2_1069_, lean_object* v_h__3_1070_, lean_object* v_h__4_1071_, lean_object* v_h__5_1072_){
_start:
{
uint8_t v_x_51__boxed_1073_; lean_object* v_res_1074_; 
v_x_51__boxed_1073_ = lean_unbox(v_x_1067_);
v_res_1074_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___redArg(v_x_51__boxed_1073_, v_h__1_1068_, v_h__2_1069_, v_h__3_1070_, v_h__4_1071_, v_h__5_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(lean_object* v_motive_1075_, uint8_t v_x_1076_, lean_object* v_h__1_1077_, lean_object* v_h__2_1078_, lean_object* v_h__3_1079_, lean_object* v_h__4_1080_, lean_object* v_h__5_1081_){
_start:
{
switch(v_x_1076_)
{
case 0:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_h__5_1081_);
lean_dec(v_h__4_1080_);
lean_dec(v_h__3_1079_);
lean_dec(v_h__2_1078_);
v___x_1082_ = lean_box(0);
v___x_1083_ = lean_apply_1(v_h__1_1077_, v___x_1082_);
return v___x_1083_;
}
case 1:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v_h__5_1081_);
lean_dec(v_h__4_1080_);
lean_dec(v_h__3_1079_);
lean_dec(v_h__1_1077_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_apply_1(v_h__2_1078_, v___x_1084_);
return v___x_1085_;
}
case 2:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v_h__5_1081_);
lean_dec(v_h__4_1080_);
lean_dec(v_h__2_1078_);
lean_dec(v_h__1_1077_);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_apply_1(v_h__3_1079_, v___x_1086_);
return v___x_1087_;
}
case 3:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec(v_h__5_1081_);
lean_dec(v_h__3_1079_);
lean_dec(v_h__2_1078_);
lean_dec(v_h__1_1077_);
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_apply_1(v_h__4_1080_, v___x_1088_);
return v___x_1089_;
}
default: 
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v_h__4_1080_);
lean_dec(v_h__3_1079_);
lean_dec(v_h__2_1078_);
lean_dec(v_h__1_1077_);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_apply_1(v_h__5_1081_, v___x_1090_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter___boxed(lean_object* v_motive_1092_, lean_object* v_x_1093_, lean_object* v_h__1_1094_, lean_object* v_h__2_1095_, lean_object* v_h__3_1096_, lean_object* v_h__4_1097_, lean_object* v_h__5_1098_){
_start:
{
uint8_t v_x_74__boxed_1099_; lean_object* v_res_1100_; 
v_x_74__boxed_1099_ = lean_unbox(v_x_1093_);
v_res_1100_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_atomicness_match__1_splitter(v_motive_1092_, v_x_74__boxed_1099_, v_h__1_1094_, v_h__2_1095_, v_h__3_1096_, v_h__4_1097_, v_h__5_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg(lean_object* v_t_1101_, lean_object* v_failure_1102_, lean_object* v_newline_1103_, lean_object* v_text_1104_, lean_object* v_tagged_1105_, lean_object* v_flattened_1106_, lean_object* v_unflattenable_1107_, lean_object* v_indented_1108_, lean_object* v_aligned_1109_, lean_object* v_unindented_1110_, lean_object* v_full_1111_, lean_object* v_free_1112_, lean_object* v_guarded_1113_, lean_object* v_costing_1114_, lean_object* v_either_1115_, lean_object* v_append_1116_){
_start:
{
switch(lean_obj_tag(v_t_1101_))
{
case 0:
{
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
lean_inc(v_failure_1102_);
return v_failure_1102_;
}
case 1:
{
lean_object* v_f_1117_; lean_object* v___x_1118_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
v_f_1117_ = lean_ctor_get(v_t_1101_, 2);
lean_inc_ref(v_f_1117_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1118_ = lean_apply_1(v_newline_1103_, v_f_1117_);
return v___x_1118_;
}
case 2:
{
lean_object* v_s_1119_; lean_object* v___x_1120_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_newline_1103_);
v_s_1119_ = lean_ctor_get(v_t_1101_, 2);
lean_inc_ref(v_s_1119_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1120_ = lean_apply_1(v_text_1104_, v_s_1119_);
return v___x_1120_;
}
case 3:
{
lean_object* v_id_1121_; lean_object* v_d_1122_; lean_object* v___x_1123_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_id_1121_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_id_1121_);
v_d_1122_ = lean_ctor_get(v_t_1101_, 3);
lean_inc(v_d_1122_);
lean_dec_ref_known(v_t_1101_, 4);
v___x_1123_ = lean_apply_2(v_tagged_1105_, v_id_1121_, v_d_1122_);
return v___x_1123_;
}
case 4:
{
lean_object* v_d_1124_; lean_object* v___x_1125_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_d_1124_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_d_1124_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1125_ = lean_apply_1(v_flattened_1106_, v_d_1124_);
return v___x_1125_;
}
case 5:
{
lean_object* v_d_1126_; lean_object* v___x_1127_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_d_1126_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_d_1126_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1127_ = lean_apply_1(v_unflattenable_1107_, v_d_1126_);
return v___x_1127_;
}
case 6:
{
lean_object* v_n_1128_; uint8_t v_isCumulative_1129_; lean_object* v_d_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_n_1128_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_n_1128_);
v_isCumulative_1129_ = lean_ctor_get_uint8(v_t_1101_, sizeof(void*)*4 + 3);
v_d_1130_ = lean_ctor_get(v_t_1101_, 3);
lean_inc(v_d_1130_);
lean_dec_ref_known(v_t_1101_, 4);
v___x_1131_ = lean_box(v_isCumulative_1129_);
v___x_1132_ = lean_apply_3(v_indented_1108_, v_n_1128_, v___x_1131_, v_d_1130_);
return v___x_1132_;
}
case 7:
{
lean_object* v_d_1133_; lean_object* v___x_1134_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_d_1133_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_d_1133_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1134_ = lean_apply_1(v_aligned_1109_, v_d_1133_);
return v___x_1134_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1135_; lean_object* v_d_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_onlyNonCumulative_1135_ = lean_ctor_get_uint8(v_t_1101_, sizeof(void*)*3 + 3);
v_d_1136_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_d_1136_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1137_ = lean_box(v_onlyNonCumulative_1135_);
v___x_1138_ = lean_apply_2(v_unindented_1110_, v___x_1137_, v_d_1136_);
return v___x_1138_;
}
case 9:
{
lean_object* v_d_1139_; lean_object* v___x_1140_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_d_1139_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_d_1139_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1140_ = lean_apply_1(v_full_1111_, v_d_1139_);
return v___x_1140_;
}
case 10:
{
lean_object* v_d_1141_; lean_object* v___x_1142_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_d_1141_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_d_1141_);
lean_dec_ref_known(v_t_1101_, 3);
v___x_1142_ = lean_apply_1(v_free_1112_, v_d_1141_);
return v___x_1142_;
}
case 11:
{
lean_object* v_p_1143_; lean_object* v_d_1144_; lean_object* v___x_1145_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_p_1143_ = lean_ctor_get(v_t_1101_, 2);
lean_inc_ref(v_p_1143_);
v_d_1144_ = lean_ctor_get(v_t_1101_, 3);
lean_inc(v_d_1144_);
lean_dec_ref_known(v_t_1101_, 4);
v___x_1145_ = lean_apply_2(v_guarded_1113_, v_p_1143_, v_d_1144_);
return v___x_1145_;
}
case 12:
{
lean_object* v_cost_1146_; lean_object* v_d_1147_; lean_object* v___x_1148_; 
lean_dec(v_append_1116_);
lean_dec(v_either_1115_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_cost_1146_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_cost_1146_);
v_d_1147_ = lean_ctor_get(v_t_1101_, 3);
lean_inc(v_d_1147_);
lean_dec_ref_known(v_t_1101_, 4);
v___x_1148_ = lean_apply_2(v_costing_1114_, v_cost_1146_, v_d_1147_);
return v___x_1148_;
}
case 13:
{
lean_object* v_a_1149_; lean_object* v_b_1150_; lean_object* v___x_1151_; 
lean_dec(v_append_1116_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_a_1149_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_a_1149_);
v_b_1150_ = lean_ctor_get(v_t_1101_, 3);
lean_inc(v_b_1150_);
lean_dec_ref_known(v_t_1101_, 4);
v___x_1151_ = lean_apply_2(v_either_1115_, v_a_1149_, v_b_1150_);
return v___x_1151_;
}
default: 
{
lean_object* v_a_1152_; lean_object* v_b_1153_; lean_object* v___x_1154_; 
lean_dec(v_either_1115_);
lean_dec(v_costing_1114_);
lean_dec(v_guarded_1113_);
lean_dec(v_free_1112_);
lean_dec(v_full_1111_);
lean_dec(v_unindented_1110_);
lean_dec(v_aligned_1109_);
lean_dec(v_indented_1108_);
lean_dec(v_unflattenable_1107_);
lean_dec(v_flattened_1106_);
lean_dec(v_tagged_1105_);
lean_dec(v_text_1104_);
lean_dec(v_newline_1103_);
v_a_1152_ = lean_ctor_get(v_t_1101_, 2);
lean_inc(v_a_1152_);
v_b_1153_ = lean_ctor_get(v_t_1101_, 3);
lean_inc(v_b_1153_);
lean_dec_ref_known(v_t_1101_, 4);
v___x_1154_ = lean_apply_2(v_append_1116_, v_a_1152_, v_b_1153_);
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___redArg___boxed(lean_object* v_t_1155_, lean_object* v_failure_1156_, lean_object* v_newline_1157_, lean_object* v_text_1158_, lean_object* v_tagged_1159_, lean_object* v_flattened_1160_, lean_object* v_unflattenable_1161_, lean_object* v_indented_1162_, lean_object* v_aligned_1163_, lean_object* v_unindented_1164_, lean_object* v_full_1165_, lean_object* v_free_1166_, lean_object* v_guarded_1167_, lean_object* v_costing_1168_, lean_object* v_either_1169_, lean_object* v_append_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Fmt_Doc_casesOn___override___redArg(v_t_1155_, v_failure_1156_, v_newline_1157_, v_text_1158_, v_tagged_1159_, v_flattened_1160_, v_unflattenable_1161_, v_indented_1162_, v_aligned_1163_, v_unindented_1164_, v_full_1165_, v_free_1166_, v_guarded_1167_, v_costing_1168_, v_either_1169_, v_append_1170_);
lean_dec(v_failure_1156_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override(lean_object* v_00_u03c4_1172_, lean_object* v_motive_1173_, lean_object* v_t_1174_, lean_object* v_failure_1175_, lean_object* v_newline_1176_, lean_object* v_text_1177_, lean_object* v_tagged_1178_, lean_object* v_flattened_1179_, lean_object* v_unflattenable_1180_, lean_object* v_indented_1181_, lean_object* v_aligned_1182_, lean_object* v_unindented_1183_, lean_object* v_full_1184_, lean_object* v_free_1185_, lean_object* v_guarded_1186_, lean_object* v_costing_1187_, lean_object* v_either_1188_, lean_object* v_append_1189_){
_start:
{
switch(lean_obj_tag(v_t_1174_))
{
case 0:
{
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
lean_inc(v_failure_1175_);
return v_failure_1175_;
}
case 1:
{
lean_object* v_f_1190_; lean_object* v___x_1191_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
v_f_1190_ = lean_ctor_get(v_t_1174_, 2);
lean_inc_ref(v_f_1190_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1191_ = lean_apply_1(v_newline_1176_, v_f_1190_);
return v___x_1191_;
}
case 2:
{
lean_object* v_s_1192_; lean_object* v___x_1193_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_newline_1176_);
v_s_1192_ = lean_ctor_get(v_t_1174_, 2);
lean_inc_ref(v_s_1192_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1193_ = lean_apply_1(v_text_1177_, v_s_1192_);
return v___x_1193_;
}
case 3:
{
lean_object* v_id_1194_; lean_object* v_d_1195_; lean_object* v___x_1196_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_id_1194_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_id_1194_);
v_d_1195_ = lean_ctor_get(v_t_1174_, 3);
lean_inc(v_d_1195_);
lean_dec_ref_known(v_t_1174_, 4);
v___x_1196_ = lean_apply_2(v_tagged_1178_, v_id_1194_, v_d_1195_);
return v___x_1196_;
}
case 4:
{
lean_object* v_d_1197_; lean_object* v___x_1198_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_d_1197_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_d_1197_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1198_ = lean_apply_1(v_flattened_1179_, v_d_1197_);
return v___x_1198_;
}
case 5:
{
lean_object* v_d_1199_; lean_object* v___x_1200_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_d_1199_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_d_1199_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1200_ = lean_apply_1(v_unflattenable_1180_, v_d_1199_);
return v___x_1200_;
}
case 6:
{
lean_object* v_n_1201_; uint8_t v_isCumulative_1202_; lean_object* v_d_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_n_1201_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_n_1201_);
v_isCumulative_1202_ = lean_ctor_get_uint8(v_t_1174_, sizeof(void*)*4 + 3);
v_d_1203_ = lean_ctor_get(v_t_1174_, 3);
lean_inc(v_d_1203_);
lean_dec_ref_known(v_t_1174_, 4);
v___x_1204_ = lean_box(v_isCumulative_1202_);
v___x_1205_ = lean_apply_3(v_indented_1181_, v_n_1201_, v___x_1204_, v_d_1203_);
return v___x_1205_;
}
case 7:
{
lean_object* v_d_1206_; lean_object* v___x_1207_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_d_1206_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_d_1206_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1207_ = lean_apply_1(v_aligned_1182_, v_d_1206_);
return v___x_1207_;
}
case 8:
{
uint8_t v_onlyNonCumulative_1208_; lean_object* v_d_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_onlyNonCumulative_1208_ = lean_ctor_get_uint8(v_t_1174_, sizeof(void*)*3 + 3);
v_d_1209_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_d_1209_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1210_ = lean_box(v_onlyNonCumulative_1208_);
v___x_1211_ = lean_apply_2(v_unindented_1183_, v___x_1210_, v_d_1209_);
return v___x_1211_;
}
case 9:
{
lean_object* v_d_1212_; lean_object* v___x_1213_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_d_1212_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_d_1212_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1213_ = lean_apply_1(v_full_1184_, v_d_1212_);
return v___x_1213_;
}
case 10:
{
lean_object* v_d_1214_; lean_object* v___x_1215_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_d_1214_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_d_1214_);
lean_dec_ref_known(v_t_1174_, 3);
v___x_1215_ = lean_apply_1(v_free_1185_, v_d_1214_);
return v___x_1215_;
}
case 11:
{
lean_object* v_p_1216_; lean_object* v_d_1217_; lean_object* v___x_1218_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_p_1216_ = lean_ctor_get(v_t_1174_, 2);
lean_inc_ref(v_p_1216_);
v_d_1217_ = lean_ctor_get(v_t_1174_, 3);
lean_inc(v_d_1217_);
lean_dec_ref_known(v_t_1174_, 4);
v___x_1218_ = lean_apply_2(v_guarded_1186_, v_p_1216_, v_d_1217_);
return v___x_1218_;
}
case 12:
{
lean_object* v_cost_1219_; lean_object* v_d_1220_; lean_object* v___x_1221_; 
lean_dec(v_append_1189_);
lean_dec(v_either_1188_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_cost_1219_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_cost_1219_);
v_d_1220_ = lean_ctor_get(v_t_1174_, 3);
lean_inc(v_d_1220_);
lean_dec_ref_known(v_t_1174_, 4);
v___x_1221_ = lean_apply_2(v_costing_1187_, v_cost_1219_, v_d_1220_);
return v___x_1221_;
}
case 13:
{
lean_object* v_a_1222_; lean_object* v_b_1223_; lean_object* v___x_1224_; 
lean_dec(v_append_1189_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_a_1222_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_a_1222_);
v_b_1223_ = lean_ctor_get(v_t_1174_, 3);
lean_inc(v_b_1223_);
lean_dec_ref_known(v_t_1174_, 4);
v___x_1224_ = lean_apply_2(v_either_1188_, v_a_1222_, v_b_1223_);
return v___x_1224_;
}
default: 
{
lean_object* v_a_1225_; lean_object* v_b_1226_; lean_object* v___x_1227_; 
lean_dec(v_either_1188_);
lean_dec(v_costing_1187_);
lean_dec(v_guarded_1186_);
lean_dec(v_free_1185_);
lean_dec(v_full_1184_);
lean_dec(v_unindented_1183_);
lean_dec(v_aligned_1182_);
lean_dec(v_indented_1181_);
lean_dec(v_unflattenable_1180_);
lean_dec(v_flattened_1179_);
lean_dec(v_tagged_1178_);
lean_dec(v_text_1177_);
lean_dec(v_newline_1176_);
v_a_1225_ = lean_ctor_get(v_t_1174_, 2);
lean_inc(v_a_1225_);
v_b_1226_ = lean_ctor_get(v_t_1174_, 3);
lean_inc(v_b_1226_);
lean_dec_ref_known(v_t_1174_, 4);
v___x_1227_ = lean_apply_2(v_append_1189_, v_a_1225_, v_b_1226_);
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_casesOn___override___boxed(lean_object** _args){
lean_object* v_00_u03c4_1228_ = _args[0];
lean_object* v_motive_1229_ = _args[1];
lean_object* v_t_1230_ = _args[2];
lean_object* v_failure_1231_ = _args[3];
lean_object* v_newline_1232_ = _args[4];
lean_object* v_text_1233_ = _args[5];
lean_object* v_tagged_1234_ = _args[6];
lean_object* v_flattened_1235_ = _args[7];
lean_object* v_unflattenable_1236_ = _args[8];
lean_object* v_indented_1237_ = _args[9];
lean_object* v_aligned_1238_ = _args[10];
lean_object* v_unindented_1239_ = _args[11];
lean_object* v_full_1240_ = _args[12];
lean_object* v_free_1241_ = _args[13];
lean_object* v_guarded_1242_ = _args[14];
lean_object* v_costing_1243_ = _args[15];
lean_object* v_either_1244_ = _args[16];
lean_object* v_append_1245_ = _args[17];
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Fmt_Doc_casesOn___override(v_00_u03c4_1228_, v_motive_1229_, v_t_1230_, v_failure_1231_, v_newline_1232_, v_text_1233_, v_tagged_1234_, v_flattened_1235_, v_unflattenable_1236_, v_indented_1237_, v_aligned_1238_, v_unindented_1239_, v_full_1240_, v_free_1241_, v_guarded_1242_, v_costing_1243_, v_either_1244_, v_append_1245_);
lean_dec(v_failure_1231_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_failure___override(lean_object* v_00_u03c4_1247_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_box(0);
return v___x_1248_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_newline___override___redArg___lam__0(uint8_t v_x_1249_){
_start:
{
uint8_t v___x_1250_; uint8_t v___x_1251_; uint8_t v___x_1252_; uint8_t v___x_1253_; 
v___x_1250_ = 1;
v___x_1251_ = lean_uint8_land(v_x_1249_, v___x_1250_);
v___x_1252_ = 0;
v___x_1253_ = lean_uint8_dec_eq(v___x_1251_, v___x_1252_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; 
v___x_1254_ = 1;
return v___x_1254_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg___lam__0___boxed(lean_object* v_x_1256_){
_start:
{
uint8_t v_x_978__boxed_1257_; uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_x_978__boxed_1257_ = lean_unbox(v_x_1256_);
v_res_1258_ = l_Lean_Fmt_Doc_newline___override___redArg___lam__0(v_x_978__boxed_1257_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override___redArg(lean_object* v_f_1263_){
_start:
{
lean_object* v___f_1264_; lean_object* v___x_1265_; uint8_t v___y_1267_; uint8_t v___y_1268_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; uint8_t v___y_1275_; 
v___f_1264_ = ((lean_object*)(l_Lean_Fmt_Doc_newline___override___redArg___closed__0));
v___x_1265_ = ((lean_object*)(l_Lean_Fmt_Doc_newline___override___redArg___closed__1));
v___x_1271_ = lean_string_utf8_byte_size(v_f_1263_);
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_nat_dec_eq(v___x_1271_, v___x_1272_);
if (v___x_1273_ == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = 2;
v___y_1275_ = v___x_1278_;
goto v___jp_1274_;
}
else
{
uint8_t v___x_1279_; 
v___x_1279_ = 1;
v___y_1275_ = v___x_1279_;
goto v___jp_1274_;
}
v___jp_1266_:
{
uint8_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = 1;
v___x_1270_ = lean_alloc_ctor(1, 3, 3);
lean_ctor_set(v___x_1270_, 0, v___f_1264_);
lean_ctor_set(v___x_1270_, 1, v___x_1265_);
lean_ctor_set(v___x_1270_, 2, v_f_1263_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*3, v___y_1267_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*3 + 1, v___y_1268_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*3 + 2, v___x_1269_);
return v___x_1270_;
}
v___jp_1274_:
{
if (v___x_1273_ == 0)
{
uint8_t v___x_1276_; 
v___x_1276_ = 0;
v___y_1267_ = v___y_1275_;
v___y_1268_ = v___x_1276_;
goto v___jp_1266_;
}
else
{
uint8_t v___x_1277_; 
v___x_1277_ = 1;
v___y_1267_ = v___y_1275_;
v___y_1268_ = v___x_1277_;
goto v___jp_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_newline___override(lean_object* v_00_u03c4_1280_, lean_object* v_f_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Fmt_Doc_newline___override___redArg(v_f_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_text___override___redArg___lam__0(lean_object* v_s_1283_, uint8_t v_state_1284_){
_start:
{
uint8_t v___x_1285_; uint8_t v___x_1286_; uint8_t v___x_1287_; uint8_t v___x_1288_; 
v___x_1285_ = 2;
v___x_1286_ = lean_uint8_land(v_state_1284_, v___x_1285_);
v___x_1287_ = 0;
v___x_1288_ = lean_uint8_dec_eq(v___x_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; uint8_t v___x_1290_; uint8_t v___x_1291_; 
v___x_1289_ = 1;
v___x_1290_ = lean_uint8_land(v_state_1284_, v___x_1289_);
v___x_1291_ = lean_uint8_dec_eq(v___x_1290_, v___x_1287_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1292_ = lean_string_utf8_byte_size(v_s_1283_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_nat_dec_eq(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = 1;
return v___x_1295_;
}
else
{
return v___x_1291_;
}
}
else
{
return v___x_1291_;
}
}
else
{
uint8_t v___x_1296_; uint8_t v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = 1;
v___x_1297_ = lean_uint8_land(v_state_1284_, v___x_1296_);
v___x_1298_ = lean_uint8_dec_eq(v___x_1297_, v___x_1287_);
if (v___x_1298_ == 0)
{
return v___x_1288_;
}
else
{
uint8_t v___x_1299_; 
v___x_1299_ = 0;
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg___lam__0___boxed(lean_object* v_s_1300_, lean_object* v_state_1301_){
_start:
{
uint8_t v_state_boxed_1302_; uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_state_boxed_1302_ = lean_unbox(v_state_1301_);
v_res_1303_ = l_Lean_Fmt_Doc_text___override___redArg___lam__0(v_s_1300_, v_state_boxed_1302_);
lean_dec_ref(v_s_1300_);
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override___redArg(lean_object* v_s_1307_){
_start:
{
lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___y_1312_; uint8_t v___y_1313_; lean_object* v___x_1316_; uint8_t v___x_1317_; uint8_t v___y_1319_; 
lean_inc_ref(v_s_1307_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_Fmt_Doc_text___override___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1308_, 0, v_s_1307_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
v___x_1316_ = lean_string_utf8_byte_size(v_s_1307_);
v___x_1317_ = lean_nat_dec_eq(v___x_1316_, v___x_1309_);
if (v___x_1317_ == 0)
{
uint8_t v___x_1322_; 
v___x_1322_ = 2;
v___y_1319_ = v___x_1322_;
goto v___jp_1318_;
}
else
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
v___y_1319_ = v___x_1323_;
goto v___jp_1318_;
}
v___jp_1311_:
{
uint8_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = 0;
v___x_1315_ = lean_alloc_ctor(2, 3, 3);
lean_ctor_set(v___x_1315_, 0, v___f_1308_);
lean_ctor_set(v___x_1315_, 1, v___x_1310_);
lean_ctor_set(v___x_1315_, 2, v_s_1307_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*3, v___y_1312_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*3 + 1, v___y_1313_);
lean_ctor_set_uint8(v___x_1315_, sizeof(void*)*3 + 2, v___x_1314_);
return v___x_1315_;
}
v___jp_1318_:
{
if (v___x_1317_ == 0)
{
uint8_t v___x_1320_; 
v___x_1320_ = 0;
v___y_1312_ = v___y_1319_;
v___y_1313_ = v___x_1320_;
goto v___jp_1311_;
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = 1;
v___y_1312_ = v___y_1319_;
v___y_1313_ = v___x_1321_;
goto v___jp_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_text___override(lean_object* v_00_u03c4_1324_, lean_object* v_s_1325_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Fmt_Doc_text___override___redArg(v_s_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_tagged___override___redArg___lam__0(uint8_t v_x_1327_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = 0;
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg___lam__0___boxed(lean_object* v_x_1329_){
_start:
{
uint8_t v_x_1106__boxed_1330_; uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_x_1106__boxed_1330_ = lean_unbox(v_x_1329_);
v_res_1331_ = l_Lean_Fmt_Doc_tagged___override___redArg___lam__0(v_x_1106__boxed_1330_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override___redArg(lean_object* v_x_1333_){
_start:
{
switch(lean_obj_tag(v_x_1333_))
{
case 0:
{
uint8_t v___x_1334_; 
v___x_1334_ = 0;
return v___x_1334_;
}
case 3:
{
uint8_t v_atomicness_1335_; 
v_atomicness_1335_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*4 + 2);
return v_atomicness_1335_;
}
case 6:
{
uint8_t v_atomicness_1336_; 
v_atomicness_1336_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*4 + 2);
return v_atomicness_1336_;
}
case 11:
{
uint8_t v_atomicness_1337_; 
v_atomicness_1337_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*4 + 2);
return v_atomicness_1337_;
}
case 12:
{
uint8_t v_atomicness_1338_; 
v_atomicness_1338_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*4 + 2);
return v_atomicness_1338_;
}
case 13:
{
uint8_t v_atomicness_1339_; 
v_atomicness_1339_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*4 + 2);
return v_atomicness_1339_;
}
case 14:
{
uint8_t v_atomicness_1340_; 
v_atomicness_1340_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*4 + 2);
return v_atomicness_1340_;
}
default: 
{
uint8_t v_atomicness_1341_; 
v_atomicness_1341_ = lean_ctor_get_uint8(v_x_1333_, sizeof(void*)*3 + 2);
return v_atomicness_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___redArg___boxed(lean_object* v_x_1342_){
_start:
{
uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_res_1343_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_1342_);
lean_dec(v_x_1342_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(lean_object* v_x_1345_){
_start:
{
if (lean_obj_tag(v_x_1345_) == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_box(0);
return v___x_1346_;
}
else
{
lean_object* v_maxNewlineCount_x3f_1347_; 
v_maxNewlineCount_x3f_1347_ = lean_ctor_get(v_x_1345_, 1);
lean_inc(v_maxNewlineCount_x3f_1347_);
return v_maxNewlineCount_x3f_1347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg___boxed(lean_object* v_x_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_1348_);
lean_dec(v_x_1348_);
return v_res_1349_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(lean_object* v_x_1350_){
_start:
{
switch(lean_obj_tag(v_x_1350_))
{
case 0:
{
uint8_t v___x_1351_; 
v___x_1351_ = 1;
return v___x_1351_;
}
case 3:
{
uint8_t v_alwaysNonEmptiness_1352_; 
v_alwaysNonEmptiness_1352_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1352_;
}
case 6:
{
uint8_t v_alwaysNonEmptiness_1353_; 
v_alwaysNonEmptiness_1353_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1353_;
}
case 11:
{
uint8_t v_alwaysNonEmptiness_1354_; 
v_alwaysNonEmptiness_1354_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1354_;
}
case 12:
{
uint8_t v_alwaysNonEmptiness_1355_; 
v_alwaysNonEmptiness_1355_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1355_;
}
case 13:
{
uint8_t v_alwaysNonEmptiness_1356_; 
v_alwaysNonEmptiness_1356_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1356_;
}
case 14:
{
uint8_t v_alwaysNonEmptiness_1357_; 
v_alwaysNonEmptiness_1357_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*4 + 1);
return v_alwaysNonEmptiness_1357_;
}
default: 
{
uint8_t v_alwaysNonEmptiness_1358_; 
v_alwaysNonEmptiness_1358_ = lean_ctor_get_uint8(v_x_1350_, sizeof(void*)*3 + 1);
return v_alwaysNonEmptiness_1358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg___boxed(lean_object* v_x_1359_){
_start:
{
uint8_t v_res_1360_; lean_object* v_r_1361_; 
v_res_1360_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_1359_);
lean_dec(v_x_1359_);
v_r_1361_ = lean_box(v_res_1360_);
return v_r_1361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(lean_object* v_x_1362_){
_start:
{
switch(lean_obj_tag(v_x_1362_))
{
case 0:
{
uint8_t v___x_1363_; 
v___x_1363_ = 2;
return v___x_1363_;
}
case 3:
{
uint8_t v_alwaysEmptiness_1364_; 
v_alwaysEmptiness_1364_ = lean_ctor_get_uint8(v_x_1362_, sizeof(void*)*4);
return v_alwaysEmptiness_1364_;
}
case 6:
{
uint8_t v_alwaysEmptiness_1365_; 
v_alwaysEmptiness_1365_ = lean_ctor_get_uint8(v_x_1362_, sizeof(void*)*4);
return v_alwaysEmptiness_1365_;
}
case 11:
{
uint8_t v_alwaysEmptiness_1366_; 
v_alwaysEmptiness_1366_ = lean_ctor_get_uint8(v_x_1362_, sizeof(void*)*4);
return v_alwaysEmptiness_1366_;
}
case 12:
{
uint8_t v_alwaysEmptiness_1367_; 
v_alwaysEmptiness_1367_ = lean_ctor_get_uint8(v_x_1362_, sizeof(void*)*4);
return v_alwaysEmptiness_1367_;
}
case 13:
{
uint8_t v_alwaysEmptiness_1368_; 
v_alwaysEmptiness_1368_ = lean_ctor_get_uint8(v_x_1362_, sizeof(void*)*4);
return v_alwaysEmptiness_1368_;
}
case 14:
{
uint8_t v_alwaysEmptiness_1369_; 
v_alwaysEmptiness_1369_ = lean_ctor_get_uint8(v_x_1362_, sizeof(void*)*4);
return v_alwaysEmptiness_1369_;
}
default: 
{
uint8_t v_alwaysEmptiness_1370_; 
v_alwaysEmptiness_1370_ = lean_ctor_get_uint8(v_x_1362_, sizeof(void*)*3);
return v_alwaysEmptiness_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg___boxed(lean_object* v_x_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_1371_);
lean_dec(v_x_1371_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override___redArg(lean_object* v_id_1375_, lean_object* v_d_1376_){
_start:
{
lean_object* v___f_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; 
v___f_1377_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1378_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1376_);
v___x_1379_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1376_);
v___x_1380_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1376_);
v___x_1381_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1376_);
v___x_1382_ = lean_alloc_ctor(3, 4, 3);
lean_ctor_set(v___x_1382_, 0, v___f_1377_);
lean_ctor_set(v___x_1382_, 1, v___x_1378_);
lean_ctor_set(v___x_1382_, 2, v_id_1375_);
lean_ctor_set(v___x_1382_, 3, v_d_1376_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*4, v___x_1379_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*4 + 1, v___x_1380_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*4 + 2, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_tagged___override(lean_object* v_00_u03c4_1383_, lean_object* v_id_1384_, lean_object* v_d_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_Fmt_Doc_tagged___override___redArg(v_id_1384_, v_d_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override___redArg(lean_object* v_d_1387_){
_start:
{
lean_object* v___f_1388_; lean_object* v___x_1389_; uint8_t v___y_1391_; uint8_t v___x_1399_; 
v___f_1388_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1389_ = ((lean_object*)(l_Lean_Fmt_Doc_text___override___redArg___closed__0));
v___x_1399_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1387_);
if (v___x_1399_ == 1)
{
uint8_t v___x_1400_; 
v___x_1400_ = 0;
v___y_1391_ = v___x_1400_;
goto v___jp_1390_;
}
else
{
v___y_1391_ = v___x_1399_;
goto v___jp_1390_;
}
v___jp_1390_:
{
uint8_t v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1387_);
v___x_1393_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1387_);
switch(v___x_1393_)
{
case 1:
{
uint8_t v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = 0;
v___x_1395_ = lean_alloc_ctor(4, 3, 3);
lean_ctor_set(v___x_1395_, 0, v___f_1388_);
lean_ctor_set(v___x_1395_, 1, v___x_1389_);
lean_ctor_set(v___x_1395_, 2, v_d_1387_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3, v___y_1391_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3 + 1, v___x_1392_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*3 + 2, v___x_1394_);
return v___x_1395_;
}
case 3:
{
uint8_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = 2;
v___x_1397_ = lean_alloc_ctor(4, 3, 3);
lean_ctor_set(v___x_1397_, 0, v___f_1388_);
lean_ctor_set(v___x_1397_, 1, v___x_1389_);
lean_ctor_set(v___x_1397_, 2, v_d_1387_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3, v___y_1391_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3 + 1, v___x_1392_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3 + 2, v___x_1396_);
return v___x_1397_;
}
default: 
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_ctor(4, 3, 3);
lean_ctor_set(v___x_1398_, 0, v___f_1388_);
lean_ctor_set(v___x_1398_, 1, v___x_1389_);
lean_ctor_set(v___x_1398_, 2, v_d_1387_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3, v___y_1391_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3 + 1, v___x_1392_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3 + 2, v___x_1393_);
return v___x_1398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_flattened___override(lean_object* v_00_u03c4_1401_, lean_object* v_d_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override___redArg(lean_object* v_d_1404_){
_start:
{
lean_object* v___f_1405_; lean_object* v___x_1406_; uint8_t v___y_1408_; uint8_t v___x_1416_; 
v___f_1405_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1406_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1404_);
v___x_1416_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1404_);
if (v___x_1416_ == 1)
{
uint8_t v___x_1417_; 
v___x_1417_ = 2;
v___y_1408_ = v___x_1417_;
goto v___jp_1407_;
}
else
{
v___y_1408_ = v___x_1416_;
goto v___jp_1407_;
}
v___jp_1407_:
{
uint8_t v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1404_);
v___x_1410_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1404_);
switch(v___x_1410_)
{
case 1:
{
uint8_t v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = 4;
v___x_1412_ = lean_alloc_ctor(5, 3, 3);
lean_ctor_set(v___x_1412_, 0, v___f_1405_);
lean_ctor_set(v___x_1412_, 1, v___x_1406_);
lean_ctor_set(v___x_1412_, 2, v_d_1404_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*3, v___y_1408_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*3 + 1, v___x_1409_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*3 + 2, v___x_1411_);
return v___x_1412_;
}
case 3:
{
uint8_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = 4;
v___x_1414_ = lean_alloc_ctor(5, 3, 3);
lean_ctor_set(v___x_1414_, 0, v___f_1405_);
lean_ctor_set(v___x_1414_, 1, v___x_1406_);
lean_ctor_set(v___x_1414_, 2, v_d_1404_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*3, v___y_1408_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*3 + 1, v___x_1409_);
lean_ctor_set_uint8(v___x_1414_, sizeof(void*)*3 + 2, v___x_1413_);
return v___x_1414_;
}
default: 
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_alloc_ctor(5, 3, 3);
lean_ctor_set(v___x_1415_, 0, v___f_1405_);
lean_ctor_set(v___x_1415_, 1, v___x_1406_);
lean_ctor_set(v___x_1415_, 2, v_d_1404_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*3, v___y_1408_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*3 + 1, v___x_1409_);
lean_ctor_set_uint8(v___x_1415_, sizeof(void*)*3 + 2, v___x_1410_);
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unflattenable___override(lean_object* v_00_u03c4_1418_, lean_object* v_d_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v_d_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg(lean_object* v_n_1421_, uint8_t v_isCumulative_1422_, lean_object* v_d_1423_){
_start:
{
lean_object* v___f_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; uint8_t v___x_1427_; uint8_t v___x_1428_; lean_object* v___x_1429_; 
v___f_1424_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1425_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1423_);
v___x_1426_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1423_);
v___x_1427_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1423_);
v___x_1428_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1423_);
v___x_1429_ = lean_alloc_ctor(6, 4, 4);
lean_ctor_set(v___x_1429_, 0, v___f_1424_);
lean_ctor_set(v___x_1429_, 1, v___x_1425_);
lean_ctor_set(v___x_1429_, 2, v_n_1421_);
lean_ctor_set(v___x_1429_, 3, v_d_1423_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*4, v___x_1426_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*4 + 1, v___x_1427_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*4 + 2, v___x_1428_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*4 + 3, v_isCumulative_1422_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___redArg___boxed(lean_object* v_n_1430_, lean_object* v_isCumulative_1431_, lean_object* v_d_1432_){
_start:
{
uint8_t v_isCumulative_boxed_1433_; lean_object* v_res_1434_; 
v_isCumulative_boxed_1433_ = lean_unbox(v_isCumulative_1431_);
v_res_1434_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_1430_, v_isCumulative_boxed_1433_, v_d_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override(lean_object* v_00_u03c4_1435_, lean_object* v_n_1436_, uint8_t v_isCumulative_1437_, lean_object* v_d_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_Fmt_Doc_indented___override___redArg(v_n_1436_, v_isCumulative_1437_, v_d_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_indented___override___boxed(lean_object* v_00_u03c4_1440_, lean_object* v_n_1441_, lean_object* v_isCumulative_1442_, lean_object* v_d_1443_){
_start:
{
uint8_t v_isCumulative_boxed_1444_; lean_object* v_res_1445_; 
v_isCumulative_boxed_1444_ = lean_unbox(v_isCumulative_1442_);
v_res_1445_ = l_Lean_Fmt_Doc_indented___override(v_00_u03c4_1440_, v_n_1441_, v_isCumulative_boxed_1444_, v_d_1443_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override___redArg(lean_object* v_d_1446_){
_start:
{
lean_object* v___f_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; uint8_t v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; 
v___f_1447_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1448_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1446_);
v___x_1449_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1446_);
v___x_1450_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1446_);
v___x_1451_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1446_);
v___x_1452_ = lean_alloc_ctor(7, 3, 3);
lean_ctor_set(v___x_1452_, 0, v___f_1447_);
lean_ctor_set(v___x_1452_, 1, v___x_1448_);
lean_ctor_set(v___x_1452_, 2, v_d_1446_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*3, v___x_1449_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*3 + 1, v___x_1450_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*3 + 2, v___x_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_aligned___override(lean_object* v_00_u03c4_1453_, lean_object* v_d_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Fmt_Doc_aligned___override___redArg(v_d_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg(uint8_t v_onlyNonCumulative_1456_, lean_object* v_d_1457_){
_start:
{
lean_object* v___f_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; uint8_t v___x_1461_; uint8_t v___x_1462_; lean_object* v___x_1463_; 
v___f_1458_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1459_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1457_);
v___x_1460_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1457_);
v___x_1461_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1457_);
v___x_1462_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1457_);
v___x_1463_ = lean_alloc_ctor(8, 3, 4);
lean_ctor_set(v___x_1463_, 0, v___f_1458_);
lean_ctor_set(v___x_1463_, 1, v___x_1459_);
lean_ctor_set(v___x_1463_, 2, v_d_1457_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*3, v___x_1460_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*3 + 1, v___x_1461_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*3 + 2, v___x_1462_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*3 + 3, v_onlyNonCumulative_1456_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___redArg___boxed(lean_object* v_onlyNonCumulative_1464_, lean_object* v_d_1465_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_1466_; lean_object* v_res_1467_; 
v_onlyNonCumulative_boxed_1466_ = lean_unbox(v_onlyNonCumulative_1464_);
v_res_1467_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_boxed_1466_, v_d_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override(lean_object* v_00_u03c4_1468_, uint8_t v_onlyNonCumulative_1469_, lean_object* v_d_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Fmt_Doc_unindented___override___redArg(v_onlyNonCumulative_1469_, v_d_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_unindented___override___boxed(lean_object* v_00_u03c4_1472_, lean_object* v_onlyNonCumulative_1473_, lean_object* v_d_1474_){
_start:
{
uint8_t v_onlyNonCumulative_boxed_1475_; lean_object* v_res_1476_; 
v_onlyNonCumulative_boxed_1475_ = lean_unbox(v_onlyNonCumulative_1473_);
v_res_1476_ = l_Lean_Fmt_Doc_unindented___override(v_00_u03c4_1472_, v_onlyNonCumulative_boxed_1475_, v_d_1474_);
return v_res_1476_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_full___override___redArg___lam__0(uint8_t v_x_1477_){
_start:
{
uint8_t v___x_1478_; uint8_t v___x_1479_; uint8_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1478_ = 1;
v___x_1479_ = lean_uint8_land(v_x_1477_, v___x_1478_);
v___x_1480_ = 0;
v___x_1481_ = lean_uint8_dec_eq(v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full___override___redArg___lam__0___boxed(lean_object* v_x_1482_){
_start:
{
uint8_t v_x_1242__boxed_1483_; uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_x_1242__boxed_1483_ = lean_unbox(v_x_1482_);
v_res_1484_ = l_Lean_Fmt_Doc_full___override___redArg___lam__0(v_x_1242__boxed_1483_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full___override___redArg(lean_object* v_d_1487_){
_start:
{
lean_object* v___f_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; uint8_t v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; 
v___f_1488_ = ((lean_object*)(l_Lean_Fmt_Doc_full___override___redArg___closed__0));
v___x_1489_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1487_);
v___x_1490_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1487_);
v___x_1491_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1487_);
v___x_1492_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1487_);
v___x_1493_ = lean_alloc_ctor(9, 3, 3);
lean_ctor_set(v___x_1493_, 0, v___f_1488_);
lean_ctor_set(v___x_1493_, 1, v___x_1489_);
lean_ctor_set(v___x_1493_, 2, v_d_1487_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*3, v___x_1490_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*3 + 1, v___x_1491_);
lean_ctor_set_uint8(v___x_1493_, sizeof(void*)*3 + 2, v___x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_full___override(lean_object* v_00_u03c4_1494_, lean_object* v_d_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_Fmt_Doc_full___override___redArg(v_d_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override___redArg(lean_object* v_d_1497_){
_start:
{
lean_object* v___f_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; uint8_t v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v___f_1498_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1499_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1497_);
v___x_1500_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1497_);
v___x_1501_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1497_);
v___x_1502_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1497_);
v___x_1503_ = lean_alloc_ctor(10, 3, 3);
lean_ctor_set(v___x_1503_, 0, v___f_1498_);
lean_ctor_set(v___x_1503_, 1, v___x_1499_);
lean_ctor_set(v___x_1503_, 2, v_d_1497_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*3, v___x_1500_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*3 + 1, v___x_1501_);
lean_ctor_set_uint8(v___x_1503_, sizeof(void*)*3 + 2, v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_free___override(lean_object* v_00_u03c4_1504_, lean_object* v_d_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Fmt_Doc_free___override___redArg(v_d_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override___redArg(lean_object* v_p_1507_, lean_object* v_d_1508_){
_start:
{
lean_object* v___f_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; uint8_t v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; 
v___f_1509_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1510_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1508_);
v___x_1511_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1508_);
v___x_1512_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1508_);
v___x_1513_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1508_);
v___x_1514_ = lean_alloc_ctor(11, 4, 3);
lean_ctor_set(v___x_1514_, 0, v___f_1509_);
lean_ctor_set(v___x_1514_, 1, v___x_1510_);
lean_ctor_set(v___x_1514_, 2, v_p_1507_);
lean_ctor_set(v___x_1514_, 3, v_d_1508_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*4, v___x_1511_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*4 + 1, v___x_1512_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*4 + 2, v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_guarded___override(lean_object* v_00_u03c4_1515_, lean_object* v_p_1516_, lean_object* v_d_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Fmt_Doc_guarded___override___redArg(v_p_1516_, v_d_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override___redArg(lean_object* v_cost_1519_, lean_object* v_d_1520_){
_start:
{
lean_object* v___f_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; uint8_t v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v___f_1521_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___x_1522_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_d_1520_);
v___x_1523_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_1520_);
v___x_1524_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_1520_);
v___x_1525_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_1520_);
v___x_1526_ = lean_alloc_ctor(12, 4, 3);
lean_ctor_set(v___x_1526_, 0, v___f_1521_);
lean_ctor_set(v___x_1526_, 1, v___x_1522_);
lean_ctor_set(v___x_1526_, 2, v_cost_1519_);
lean_ctor_set(v___x_1526_, 3, v_d_1520_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*4, v___x_1523_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*4 + 1, v___x_1524_);
lean_ctor_set_uint8(v___x_1526_, sizeof(void*)*4 + 2, v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_costing___override(lean_object* v_00_u03c4_1527_, lean_object* v_cost_1528_, lean_object* v_d_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Fmt_Doc_costing___override___redArg(v_cost_1528_, v_d_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__1(lean_object* v_x1_1531_, lean_object* v_x2_1532_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_nat_dec_le(v_x1_1531_, v_x2_1532_);
if (v___x_1533_ == 0)
{
lean_inc(v_x1_1531_);
return v_x1_1531_;
}
else
{
lean_inc(v_x2_1532_);
return v_x2_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg___lam__1___boxed(lean_object* v_x1_1534_, lean_object* v_x2_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Fmt_Doc_either___override___redArg___lam__1(v_x1_1534_, v_x2_1535_);
lean_dec(v_x2_1535_);
lean_dec(v_x1_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override___redArg(lean_object* v_a_1538_, lean_object* v_b_1539_){
_start:
{
lean_object* v___f_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; uint8_t v___x_1546_; uint8_t v___x_1547_; uint8_t v___x_1548_; uint8_t v___x_1549_; uint8_t v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; 
v___f_1540_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___f_1541_ = ((lean_object*)(l_Lean_Fmt_Doc_either___override___redArg___closed__0));
v___x_1542_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_1538_);
v___x_1543_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_1539_);
v___x_1544_ = l_Option_merge___redArg(v___f_1541_, v___x_1542_, v___x_1543_);
v___x_1545_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_1538_);
v___x_1546_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_1539_);
v___x_1547_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_1545_, v___x_1546_);
v___x_1548_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_1538_);
v___x_1549_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_1539_);
v___x_1550_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_1548_, v___x_1549_);
v___x_1551_ = 4;
v___x_1552_ = lean_alloc_ctor(13, 4, 3);
lean_ctor_set(v___x_1552_, 0, v___f_1540_);
lean_ctor_set(v___x_1552_, 1, v___x_1544_);
lean_ctor_set(v___x_1552_, 2, v_a_1538_);
lean_ctor_set(v___x_1552_, 3, v_b_1539_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*4, v___x_1547_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*4 + 1, v___x_1550_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*4 + 2, v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_either___override(lean_object* v_00_u03c4_1553_, lean_object* v_a_1554_, lean_object* v_b_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Fmt_Doc_either___override___redArg(v_a_1554_, v_b_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override___redArg(lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
lean_object* v___f_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; uint8_t v___x_1565_; uint8_t v___x_1566_; uint8_t v___x_1567_; uint8_t v___x_1568_; uint8_t v___x_1569_; 
v___f_1559_ = ((lean_object*)(l_Lean_Fmt_Doc_tagged___override___redArg___closed__0));
v___f_1560_ = ((lean_object*)(l_Lean_Fmt_instHAddTagIdNat___closed__0));
v___x_1561_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_a_1557_);
v___x_1562_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_b_1558_);
v___x_1563_ = l_Option_merge___redArg(v___f_1560_, v___x_1561_, v___x_1562_);
v___x_1564_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_a_1557_);
v___x_1565_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_b_1558_);
v___x_1566_ = l_Lean_Fmt_Doc_AlwaysEmptiness_max(v___x_1564_, v___x_1565_);
v___x_1567_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_a_1557_);
v___x_1568_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_b_1558_);
v___x_1569_ = l_Lean_Fmt_Doc_AlwaysNonEmptiness_max(v___x_1567_, v___x_1568_);
if (v___x_1564_ == 0)
{
uint8_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_1558_);
v___x_1571_ = lean_alloc_ctor(14, 4, 3);
lean_ctor_set(v___x_1571_, 0, v___f_1559_);
lean_ctor_set(v___x_1571_, 1, v___x_1563_);
lean_ctor_set(v___x_1571_, 2, v_a_1557_);
lean_ctor_set(v___x_1571_, 3, v_b_1558_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*4, v___x_1566_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*4 + 1, v___x_1569_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*4 + 2, v___x_1570_);
return v___x_1571_;
}
else
{
if (v___x_1565_ == 0)
{
uint8_t v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_1557_);
v___x_1573_ = lean_alloc_ctor(14, 4, 3);
lean_ctor_set(v___x_1573_, 0, v___f_1559_);
lean_ctor_set(v___x_1573_, 1, v___x_1563_);
lean_ctor_set(v___x_1573_, 2, v_a_1557_);
lean_ctor_set(v___x_1573_, 3, v_b_1558_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*4, v___x_1566_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*4 + 1, v___x_1569_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*4 + 2, v___x_1572_);
return v___x_1573_;
}
else
{
uint8_t v___x_1574_; uint8_t v___x_1575_; uint8_t v___x_1576_; uint8_t v___x_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v___x_1574_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_a_1557_);
v___x_1575_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_b_1558_);
v___x_1576_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_1574_, v___x_1575_);
v___x_1577_ = 2;
v___x_1578_ = l_Lean_Fmt_Doc_Atomicness_max(v___x_1576_, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(14, 4, 3);
lean_ctor_set(v___x_1579_, 0, v___f_1559_);
lean_ctor_set(v___x_1579_, 1, v___x_1563_);
lean_ctor_set(v___x_1579_, 2, v_a_1557_);
lean_ctor_set(v___x_1579_, 3, v_b_1558_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*4, v___x_1566_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*4 + 1, v___x_1569_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*4 + 2, v___x_1578_);
return v___x_1579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_append___override(lean_object* v_00_u03c4_1580_, lean_object* v_a_1581_, lean_object* v_b_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Fmt_Doc_append___override___redArg(v_a_1581_, v_b_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___override___redArg(lean_object* v_x_1584_, uint8_t v_a_1585_){
_start:
{
if (lean_obj_tag(v_x_1584_) == 0)
{
uint8_t v___x_1586_; 
v___x_1586_ = 1;
return v___x_1586_;
}
else
{
lean_object* v_isFailure_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_isFailure_1587_ = lean_ctor_get(v_x_1584_, 0);
lean_inc_ref(v_isFailure_1587_);
lean_dec(v_x_1584_);
v___x_1588_ = lean_box(v_a_1585_);
v___x_1589_ = lean_apply_1(v_isFailure_1587_, v___x_1588_);
v___x_1590_ = lean_unbox(v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___override___redArg___boxed(lean_object* v_x_1591_, lean_object* v_a_1592_){
_start:
{
uint8_t v_a_1401__boxed_1593_; uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_a_1401__boxed_1593_ = lean_unbox(v_a_1592_);
v_res_1594_ = l_Lean_Fmt_Doc_isFailure___override___redArg(v_x_1591_, v_a_1401__boxed_1593_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isFailure___override(lean_object* v_00_u03c4_1596_, lean_object* v_x_1597_, uint8_t v_a_1598_){
_start:
{
uint8_t v___x_1599_; 
v___x_1599_ = l_Lean_Fmt_Doc_isFailure___override___redArg(v_x_1597_, v_a_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isFailure___override___boxed(lean_object* v_00_u03c4_1600_, lean_object* v_x_1601_, lean_object* v_a_1602_){
_start:
{
uint8_t v_a_1425__boxed_1603_; uint8_t v_res_1604_; lean_object* v_r_1605_; 
v_a_1425__boxed_1603_ = lean_unbox(v_a_1602_);
v_res_1604_ = l_Lean_Fmt_Doc_isFailure___override(v_00_u03c4_1600_, v_x_1601_, v_a_1425__boxed_1603_);
v_r_1605_ = lean_box(v_res_1604_);
return v_r_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(lean_object* v_00_u03c4_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___redArg(v_x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maxNewlineCount_x3f___override___boxed(lean_object* v_00_u03c4_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Fmt_Doc_maxNewlineCount_x3f___override(v_00_u03c4_1609_, v_x_1610_);
lean_dec(v_x_1610_);
return v_res_1611_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysEmptiness___override(lean_object* v_00_u03c4_1612_, lean_object* v_x_1613_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysEmptiness___override___boxed(lean_object* v_00_u03c4_1615_, lean_object* v_x_1616_){
_start:
{
uint8_t v_res_1617_; lean_object* v_r_1618_; 
v_res_1617_ = l_Lean_Fmt_Doc_alwaysEmptiness___override(v_00_u03c4_1615_, v_x_1616_);
lean_dec(v_x_1616_);
v_r_1618_ = lean_box(v_res_1617_);
return v_r_1618_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_alwaysNonEmptiness___override(lean_object* v_00_u03c4_1619_, lean_object* v_x_1620_){
_start:
{
uint8_t v___x_1621_; 
v___x_1621_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_alwaysNonEmptiness___override___boxed(lean_object* v_00_u03c4_1622_, lean_object* v_x_1623_){
_start:
{
uint8_t v_res_1624_; lean_object* v_r_1625_; 
v_res_1624_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override(v_00_u03c4_1622_, v_x_1623_);
lean_dec(v_x_1623_);
v_r_1625_ = lean_box(v_res_1624_);
return v_r_1625_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_atomicness___override(lean_object* v_00_u03c4_1626_, lean_object* v_x_1627_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_atomicness___override___boxed(lean_object* v_00_u03c4_1629_, lean_object* v_x_1630_){
_start:
{
uint8_t v_res_1631_; lean_object* v_r_1632_; 
v_res_1631_ = l_Lean_Fmt_Doc_atomicness___override(v_00_u03c4_1629_, v_x_1630_);
lean_dec(v_x_1630_);
v_r_1632_ = lean_box(v_res_1631_);
return v_r_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc_default(lean_object* v_00_u03c4_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_box(0);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedDoc(lean_object* v_a_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_box(0);
return v___x_1636_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = lean_unsigned_to_nat(2u);
v___x_1641_ = lean_nat_to_int(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_unsigned_to_nat(1u);
v___x_1643_ = lean_nat_to_int(v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg(lean_object* v_inst_1734_, lean_object* v_x_1735_, lean_object* v_prec_1736_){
_start:
{
lean_object* v___y_1738_; 
switch(lean_obj_tag(v_x_1735_))
{
case 0:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
lean_dec_ref(v_inst_1734_);
v___x_1744_ = lean_unsigned_to_nat(1024u);
v___x_1745_ = lean_nat_dec_le(v___x_1744_, v_prec_1736_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
v___x_1746_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1738_ = v___x_1746_;
goto v___jp_1737_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1738_ = v___x_1747_;
goto v___jp_1737_;
}
}
case 1:
{
lean_object* v_f_1748_; lean_object* v___y_1750_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
lean_dec_ref(v_inst_1734_);
v_f_1748_ = lean_ctor_get(v_x_1735_, 2);
lean_inc_ref(v_f_1748_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1759_ = lean_unsigned_to_nat(1024u);
v___x_1760_ = lean_nat_dec_le(v___x_1759_, v_prec_1736_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1750_ = v___x_1761_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1750_ = v___x_1762_;
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1751_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__6));
v___x_1752_ = l_String_quote(v_f_1748_);
v___x_1753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
v___x_1754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1751_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
lean_inc(v___y_1750_);
v___x_1755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___y_1750_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = 0;
v___x_1757_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set_uint8(v___x_1757_, sizeof(void*)*1, v___x_1756_);
v___x_1758_ = l_Repr_addAppParen(v___x_1757_, v_prec_1736_);
return v___x_1758_;
}
}
case 2:
{
lean_object* v_s_1763_; lean_object* v___y_1765_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
lean_dec_ref(v_inst_1734_);
v_s_1763_ = lean_ctor_get(v_x_1735_, 2);
lean_inc_ref(v_s_1763_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1774_ = lean_unsigned_to_nat(1024u);
v___x_1775_ = lean_nat_dec_le(v___x_1774_, v_prec_1736_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1765_ = v___x_1776_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1765_ = v___x_1777_;
goto v___jp_1764_;
}
v___jp_1764_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1766_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__9));
v___x_1767_ = l_String_quote(v_s_1763_);
v___x_1768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1766_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
lean_inc(v___y_1765_);
v___x_1770_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___y_1765_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = 0;
v___x_1772_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1772_, 0, v___x_1770_);
lean_ctor_set_uint8(v___x_1772_, sizeof(void*)*1, v___x_1771_);
v___x_1773_ = l_Repr_addAppParen(v___x_1772_, v_prec_1736_);
return v___x_1773_;
}
}
case 3:
{
lean_object* v_id_1778_; lean_object* v_d_1779_; lean_object* v___x_1780_; lean_object* v___y_1782_; uint8_t v___x_1795_; 
v_id_1778_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_id_1778_);
v_d_1779_ = lean_ctor_get(v_x_1735_, 3);
lean_inc(v_d_1779_);
lean_dec_ref_known(v_x_1735_, 4);
v___x_1780_ = lean_unsigned_to_nat(1024u);
v___x_1795_ = lean_nat_dec_le(v___x_1780_, v_prec_1736_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1782_ = v___x_1796_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1782_ = v___x_1797_;
goto v___jp_1781_;
}
v___jp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1783_ = lean_box(1);
v___x_1784_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__12));
v___x_1785_ = l_Nat_reprFast(v_id_1778_);
v___x_1786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1784_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
lean_ctor_set(v___x_1788_, 1, v___x_1783_);
v___x_1789_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1779_, v___x_1780_);
v___x_1790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
lean_inc(v___y_1782_);
v___x_1791_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___y_1782_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = 0;
v___x_1793_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*1, v___x_1792_);
v___x_1794_ = l_Repr_addAppParen(v___x_1793_, v_prec_1736_);
return v___x_1794_;
}
}
case 4:
{
lean_object* v_d_1798_; lean_object* v___x_1799_; lean_object* v___y_1801_; uint8_t v___x_1809_; 
v_d_1798_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_d_1798_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1799_ = lean_unsigned_to_nat(1024u);
v___x_1809_ = lean_nat_dec_le(v___x_1799_, v_prec_1736_);
if (v___x_1809_ == 0)
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1801_ = v___x_1810_;
goto v___jp_1800_;
}
else
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1801_ = v___x_1811_;
goto v___jp_1800_;
}
v___jp_1800_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1802_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__15));
v___x_1803_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1798_, v___x_1799_);
v___x_1804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
lean_inc(v___y_1801_);
v___x_1805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___y_1801_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = 0;
v___x_1807_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set_uint8(v___x_1807_, sizeof(void*)*1, v___x_1806_);
v___x_1808_ = l_Repr_addAppParen(v___x_1807_, v_prec_1736_);
return v___x_1808_;
}
}
case 5:
{
lean_object* v_d_1812_; lean_object* v___x_1813_; lean_object* v___y_1815_; uint8_t v___x_1823_; 
v_d_1812_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_d_1812_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1813_ = lean_unsigned_to_nat(1024u);
v___x_1823_ = lean_nat_dec_le(v___x_1813_, v_prec_1736_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1815_ = v___x_1824_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1815_ = v___x_1825_;
goto v___jp_1814_;
}
v___jp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1816_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__18));
v___x_1817_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1812_, v___x_1813_);
v___x_1818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
lean_inc(v___y_1815_);
v___x_1819_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1819_, 0, v___y_1815_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
v___x_1820_ = 0;
v___x_1821_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1821_, 0, v___x_1819_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*1, v___x_1820_);
v___x_1822_ = l_Repr_addAppParen(v___x_1821_, v_prec_1736_);
return v___x_1822_;
}
}
case 6:
{
lean_object* v_n_1826_; uint8_t v_isCumulative_1827_; lean_object* v_d_1828_; lean_object* v___x_1829_; lean_object* v___y_1831_; uint8_t v___x_1847_; 
v_n_1826_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_n_1826_);
v_isCumulative_1827_ = lean_ctor_get_uint8(v_x_1735_, sizeof(void*)*4 + 3);
v_d_1828_ = lean_ctor_get(v_x_1735_, 3);
lean_inc(v_d_1828_);
lean_dec_ref_known(v_x_1735_, 4);
v___x_1829_ = lean_unsigned_to_nat(1024u);
v___x_1847_ = lean_nat_dec_le(v___x_1829_, v_prec_1736_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1831_ = v___x_1848_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1831_ = v___x_1849_;
goto v___jp_1830_;
}
v___jp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1832_ = lean_box(1);
v___x_1833_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__21));
v___x_1834_ = l_Nat_reprFast(v_n_1826_);
v___x_1835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1833_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set(v___x_1837_, 1, v___x_1832_);
v___x_1838_ = l_Bool_repr___redArg(v_isCumulative_1827_);
v___x_1839_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
lean_ctor_set(v___x_1840_, 1, v___x_1832_);
v___x_1841_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1828_, v___x_1829_);
v___x_1842_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
lean_inc(v___y_1831_);
v___x_1843_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___y_1831_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = 0;
v___x_1845_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*1, v___x_1844_);
v___x_1846_ = l_Repr_addAppParen(v___x_1845_, v_prec_1736_);
return v___x_1846_;
}
}
case 7:
{
lean_object* v_d_1850_; lean_object* v___x_1851_; lean_object* v___y_1853_; uint8_t v___x_1861_; 
v_d_1850_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_d_1850_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1851_ = lean_unsigned_to_nat(1024u);
v___x_1861_ = lean_nat_dec_le(v___x_1851_, v_prec_1736_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1853_ = v___x_1862_;
goto v___jp_1852_;
}
else
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1853_ = v___x_1863_;
goto v___jp_1852_;
}
v___jp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1854_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__24));
v___x_1855_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1850_, v___x_1851_);
v___x_1856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
lean_inc(v___y_1853_);
v___x_1857_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___y_1853_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = 0;
v___x_1859_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*1, v___x_1858_);
v___x_1860_ = l_Repr_addAppParen(v___x_1859_, v_prec_1736_);
return v___x_1860_;
}
}
case 8:
{
uint8_t v_onlyNonCumulative_1864_; lean_object* v_d_1865_; lean_object* v___x_1866_; lean_object* v___y_1868_; uint8_t v___x_1880_; 
v_onlyNonCumulative_1864_ = lean_ctor_get_uint8(v_x_1735_, sizeof(void*)*3 + 3);
v_d_1865_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_d_1865_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1866_ = lean_unsigned_to_nat(1024u);
v___x_1880_ = lean_nat_dec_le(v___x_1866_, v_prec_1736_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1868_ = v___x_1881_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1868_ = v___x_1882_;
goto v___jp_1867_;
}
v___jp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1869_ = lean_box(1);
v___x_1870_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__27));
v___x_1871_ = l_Bool_repr___redArg(v_onlyNonCumulative_1864_);
v___x_1872_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v___x_1869_);
v___x_1874_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1865_, v___x_1866_);
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
lean_inc(v___y_1868_);
v___x_1876_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___y_1868_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = 0;
v___x_1878_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*1, v___x_1877_);
v___x_1879_ = l_Repr_addAppParen(v___x_1878_, v_prec_1736_);
return v___x_1879_;
}
}
case 9:
{
lean_object* v_d_1883_; lean_object* v___x_1884_; lean_object* v___y_1886_; uint8_t v___x_1894_; 
v_d_1883_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_d_1883_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1884_ = lean_unsigned_to_nat(1024u);
v___x_1894_ = lean_nat_dec_le(v___x_1884_, v_prec_1736_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1886_ = v___x_1895_;
goto v___jp_1885_;
}
else
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1886_ = v___x_1896_;
goto v___jp_1885_;
}
v___jp_1885_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1887_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__30));
v___x_1888_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1883_, v___x_1884_);
v___x_1889_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
lean_inc(v___y_1886_);
v___x_1890_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___y_1886_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = 0;
v___x_1892_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*1, v___x_1891_);
v___x_1893_ = l_Repr_addAppParen(v___x_1892_, v_prec_1736_);
return v___x_1893_;
}
}
case 10:
{
lean_object* v_d_1897_; lean_object* v___x_1898_; lean_object* v___y_1900_; uint8_t v___x_1908_; 
v_d_1897_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_d_1897_);
lean_dec_ref_known(v_x_1735_, 3);
v___x_1898_ = lean_unsigned_to_nat(1024u);
v___x_1908_ = lean_nat_dec_le(v___x_1898_, v_prec_1736_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1900_ = v___x_1909_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1900_ = v___x_1910_;
goto v___jp_1899_;
}
v___jp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1901_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__33));
v___x_1902_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1897_, v___x_1898_);
v___x_1903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
lean_inc(v___y_1900_);
v___x_1904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___y_1900_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = 0;
v___x_1906_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set_uint8(v___x_1906_, sizeof(void*)*1, v___x_1905_);
v___x_1907_ = l_Repr_addAppParen(v___x_1906_, v_prec_1736_);
return v___x_1907_;
}
}
case 11:
{
lean_object* v_d_1911_; lean_object* v___x_1912_; lean_object* v___y_1914_; uint8_t v___x_1922_; 
v_d_1911_ = lean_ctor_get(v_x_1735_, 3);
lean_inc(v_d_1911_);
lean_dec_ref_known(v_x_1735_, 4);
v___x_1912_ = lean_unsigned_to_nat(1024u);
v___x_1922_ = lean_nat_dec_le(v___x_1912_, v_prec_1736_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1914_ = v___x_1923_;
goto v___jp_1913_;
}
else
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1914_ = v___x_1924_;
goto v___jp_1913_;
}
v___jp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1915_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__38));
v___x_1916_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1911_, v___x_1912_);
v___x_1917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
lean_inc(v___y_1914_);
v___x_1918_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___y_1914_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = 0;
v___x_1920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set_uint8(v___x_1920_, sizeof(void*)*1, v___x_1919_);
v___x_1921_ = l_Repr_addAppParen(v___x_1920_, v_prec_1736_);
return v___x_1921_;
}
}
case 12:
{
lean_object* v_cost_1925_; lean_object* v_d_1926_; lean_object* v___x_1927_; lean_object* v___y_1929_; uint8_t v___x_1941_; 
v_cost_1925_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_cost_1925_);
v_d_1926_ = lean_ctor_get(v_x_1735_, 3);
lean_inc(v_d_1926_);
lean_dec_ref_known(v_x_1735_, 4);
v___x_1927_ = lean_unsigned_to_nat(1024u);
v___x_1941_ = lean_nat_dec_le(v___x_1927_, v_prec_1736_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1929_ = v___x_1942_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1929_ = v___x_1943_;
goto v___jp_1928_;
}
v___jp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1930_ = lean_box(1);
v___x_1931_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__41));
lean_inc_ref(v_inst_1734_);
v___x_1932_ = lean_apply_2(v_inst_1734_, v_cost_1925_, v___x_1927_);
v___x_1933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___x_1930_);
v___x_1935_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_d_1926_, v___x_1927_);
v___x_1936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
lean_inc(v___y_1929_);
v___x_1937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___y_1929_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = 0;
v___x_1939_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*1, v___x_1938_);
v___x_1940_ = l_Repr_addAppParen(v___x_1939_, v_prec_1736_);
return v___x_1940_;
}
}
case 13:
{
lean_object* v_a_1944_; lean_object* v_b_1945_; lean_object* v___x_1946_; lean_object* v___y_1948_; uint8_t v___x_1960_; 
v_a_1944_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_a_1944_);
v_b_1945_ = lean_ctor_get(v_x_1735_, 3);
lean_inc(v_b_1945_);
lean_dec_ref_known(v_x_1735_, 4);
v___x_1946_ = lean_unsigned_to_nat(1024u);
v___x_1960_ = lean_nat_dec_le(v___x_1946_, v_prec_1736_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1948_ = v___x_1961_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1948_ = v___x_1962_;
goto v___jp_1947_;
}
v___jp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1949_ = lean_box(1);
v___x_1950_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__44));
lean_inc_ref(v_inst_1734_);
v___x_1951_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_a_1944_, v___x_1946_);
v___x_1952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
lean_ctor_set(v___x_1953_, 1, v___x_1949_);
v___x_1954_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_b_1945_, v___x_1946_);
v___x_1955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
lean_inc(v___y_1948_);
v___x_1956_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___y_1948_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = 0;
v___x_1958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*1, v___x_1957_);
v___x_1959_ = l_Repr_addAppParen(v___x_1958_, v_prec_1736_);
return v___x_1959_;
}
}
default: 
{
lean_object* v_a_1963_; lean_object* v_b_1964_; lean_object* v___x_1965_; lean_object* v___y_1967_; uint8_t v___x_1979_; 
v_a_1963_ = lean_ctor_get(v_x_1735_, 2);
lean_inc(v_a_1963_);
v_b_1964_ = lean_ctor_get(v_x_1735_, 3);
lean_inc(v_b_1964_);
lean_dec_ref_known(v_x_1735_, 4);
v___x_1965_ = lean_unsigned_to_nat(1024u);
v___x_1979_ = lean_nat_dec_le(v___x_1965_, v_prec_1736_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__2, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__2_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__2);
v___y_1967_ = v___x_1980_;
goto v___jp_1966_;
}
else
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_obj_once(&l_Lean_Fmt_instReprDoc_repr___redArg___closed__3, &l_Lean_Fmt_instReprDoc_repr___redArg___closed__3_once, _init_l_Lean_Fmt_instReprDoc_repr___redArg___closed__3);
v___y_1967_ = v___x_1981_;
goto v___jp_1966_;
}
v___jp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1968_ = lean_box(1);
v___x_1969_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__47));
lean_inc_ref(v_inst_1734_);
v___x_1970_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_a_1963_, v___x_1965_);
v___x_1971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1968_);
v___x_1973_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1734_, v_b_1964_, v___x_1965_);
v___x_1974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
lean_inc(v___y_1967_);
v___x_1975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1967_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = 0;
v___x_1977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*1, v___x_1976_);
v___x_1978_ = l_Repr_addAppParen(v___x_1977_, v_prec_1736_);
return v___x_1978_;
}
}
}
v___jp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1739_ = ((lean_object*)(l_Lean_Fmt_instReprDoc_repr___redArg___closed__1));
lean_inc(v___y_1738_);
v___x_1740_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___y_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = 0;
v___x_1742_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*1, v___x_1741_);
v___x_1743_ = l_Repr_addAppParen(v___x_1742_, v_prec_1736_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___redArg___boxed(lean_object* v_inst_1982_, lean_object* v_x_1983_, lean_object* v_prec_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1982_, v_x_1983_, v_prec_1984_);
lean_dec(v_prec_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr(lean_object* v_00_u03c4_1986_, lean_object* v_inst_1987_, lean_object* v_x_1988_, lean_object* v_prec_1989_){
_start:
{
lean_object* v___x_1990_; 
v___x_1990_ = l_Lean_Fmt_instReprDoc_repr___redArg(v_inst_1987_, v_x_1988_, v_prec_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc_repr___boxed(lean_object* v_00_u03c4_1991_, lean_object* v_inst_1992_, lean_object* v_x_1993_, lean_object* v_prec_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Fmt_instReprDoc_repr(v_00_u03c4_1991_, v_inst_1992_, v_x_1993_, v_prec_1994_);
lean_dec(v_prec_1994_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc___redArg(lean_object* v_inst_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_1997_, 0, lean_box(0));
lean_closure_set(v___x_1997_, 1, v_inst_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instReprDoc(lean_object* v_00_u03c4_1998_, lean_object* v_inst_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = lean_alloc_closure((void*)(l_Lean_Fmt_instReprDoc_repr___boxed), 4, 2);
lean_closure_set(v___x_2000_, 0, lean_box(0));
lean_closure_set(v___x_2000_, 1, v_inst_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(lean_object* v_d_2001_){
_start:
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Fmt_Doc_alwaysEmptiness___override___redArg(v_d_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = 1;
return v___x_2003_;
}
else
{
uint8_t v___x_2004_; 
v___x_2004_ = 0;
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___redArg___boxed(lean_object* v_d_2005_){
_start:
{
uint8_t v_res_2006_; lean_object* v_r_2007_; 
v_res_2006_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_2005_);
lean_dec(v_d_2005_);
v_r_2007_ = lean_box(v_res_2006_);
return v_r_2007_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysEmpty(lean_object* v_00_u03c4_2008_, lean_object* v_d_2009_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = l_Lean_Fmt_Doc_isAlwaysEmpty___redArg(v_d_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysEmpty___boxed(lean_object* v_00_u03c4_2011_, lean_object* v_d_2012_){
_start:
{
uint8_t v_res_2013_; lean_object* v_r_2014_; 
v_res_2013_ = l_Lean_Fmt_Doc_isAlwaysEmpty(v_00_u03c4_2011_, v_d_2012_);
lean_dec(v_d_2012_);
v_r_2014_ = lean_box(v_res_2013_);
return v_r_2014_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(lean_object* v_d_2015_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Fmt_Doc_alwaysNonEmptiness___override___redArg(v_d_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; 
v___x_2017_ = 1;
return v___x_2017_;
}
else
{
uint8_t v___x_2018_; 
v___x_2018_ = 0;
return v___x_2018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg___boxed(lean_object* v_d_2019_){
_start:
{
uint8_t v_res_2020_; lean_object* v_r_2021_; 
v_res_2020_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_2019_);
lean_dec(v_d_2019_);
v_r_2021_ = lean_box(v_res_2020_);
return v_r_2021_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAlwaysNonEmpty(lean_object* v_00_u03c4_2022_, lean_object* v_d_2023_){
_start:
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty___redArg(v_d_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAlwaysNonEmpty___boxed(lean_object* v_00_u03c4_2025_, lean_object* v_d_2026_){
_start:
{
uint8_t v_res_2027_; lean_object* v_r_2028_; 
v_res_2027_ = l_Lean_Fmt_Doc_isAlwaysNonEmpty(v_00_u03c4_2025_, v_d_2026_);
lean_dec(v_d_2026_);
v_r_2028_ = lean_box(v_res_2027_);
return v_r_2028_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic___redArg(lean_object* v_d_2029_){
_start:
{
uint8_t v___x_2030_; 
v___x_2030_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2029_);
if (v___x_2030_ == 2)
{
uint8_t v___x_2031_; 
v___x_2031_ = 1;
return v___x_2031_;
}
else
{
if (v___x_2030_ == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = 1;
return v___x_2032_;
}
else
{
uint8_t v___x_2033_; 
v___x_2033_ = 0;
return v___x_2033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___redArg___boxed(lean_object* v_d_2034_){
_start:
{
uint8_t v_res_2035_; lean_object* v_r_2036_; 
v_res_2035_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_2034_);
lean_dec(v_d_2034_);
v_r_2036_ = lean_box(v_res_2035_);
return v_r_2036_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isCompoundAtomic(lean_object* v_00_u03c4_2037_, lean_object* v_d_2038_){
_start:
{
uint8_t v___x_2039_; 
v___x_2039_ = l_Lean_Fmt_Doc_isCompoundAtomic___redArg(v_d_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isCompoundAtomic___boxed(lean_object* v_00_u03c4_2040_, lean_object* v_d_2041_){
_start:
{
uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_res_2042_ = l_Lean_Fmt_Doc_isCompoundAtomic(v_00_u03c4_2040_, v_d_2041_);
lean_dec(v_d_2041_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic___redArg(lean_object* v_d_2044_){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_Fmt_Doc_atomicness___override___redArg(v_d_2044_);
if (v___x_2045_ == 0)
{
uint8_t v___x_2046_; 
v___x_2046_ = 1;
return v___x_2046_;
}
else
{
uint8_t v___x_2047_; 
v___x_2047_ = 0;
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___redArg___boxed(lean_object* v_d_2048_){
_start:
{
uint8_t v_res_2049_; lean_object* v_r_2050_; 
v_res_2049_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_2048_);
lean_dec(v_d_2048_);
v_r_2050_ = lean_box(v_res_2049_);
return v_r_2050_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_isAtomic(lean_object* v_00_u03c4_2051_, lean_object* v_d_2052_){
_start:
{
uint8_t v___x_2053_; 
v___x_2053_ = l_Lean_Fmt_Doc_isAtomic___redArg(v_d_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_isAtomic___boxed(lean_object* v_00_u03c4_2054_, lean_object* v_d_2055_){
_start:
{
uint8_t v_res_2056_; lean_object* v_r_2057_; 
v_res_2056_ = l_Lean_Fmt_Doc_isAtomic(v_00_u03c4_2054_, v_d_2055_);
lean_dec(v_d_2055_);
v_r_2057_ = lean_box(v_res_2056_);
return v_r_2057_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_empty___closed__1(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___closed__0));
v___x_2060_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_empty(lean_object* v_00_u03c4_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__1, &l_Lean_Fmt_Doc_empty___closed__1_once, _init_l_Lean_Fmt_Doc_empty___closed__1);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened___redArg(lean_object* v_d_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_inc(v_d_2063_);
v___x_2064_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_d_2063_);
v___x_2065_ = l_Lean_Fmt_Doc_either___override___redArg(v_d_2063_, v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_maybeFlattened(lean_object* v_00_u03c4_2066_, lean_object* v_d_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_Fmt_Doc_maybeFlattened___redArg(v_d_2067_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_nl___closed__1(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___closed__0));
v___x_2071_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nl(lean_object* v_00_u03c4_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_obj_once(&l_Lean_Fmt_Doc_nl___closed__1, &l_Lean_Fmt_Doc_nl___closed__1_once, _init_l_Lean_Fmt_Doc_nl___closed__1);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_break___closed__0(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = ((lean_object*)(l_Lean_Fmt_Doc_empty___closed__0));
v___x_2075_ = l_Lean_Fmt_Doc_newline___override___redArg(v___x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_break(lean_object* v_00_u03c4_2076_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_obj_once(&l_Lean_Fmt_Doc_break___closed__0, &l_Lean_Fmt_Doc_break___closed__0_once, _init_l_Lean_Fmt_Doc_break___closed__0);
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___closed__0(void){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Fmt_Doc_nl(lean_box(0));
return v___x_2078_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_hardNl___closed__1(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_2080_ = l_Lean_Fmt_Doc_unflattenable___override___redArg(v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNl(lean_object* v_00_u03c4_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__1, &l_Lean_Fmt_Doc_hardNl___closed__1_once, _init_l_Lean_Fmt_Doc_hardNl___closed__1);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested___redArg(lean_object* v_d_2083_){
_start:
{
lean_object* v___x_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_unsigned_to_nat(2u);
v___x_2085_ = 0;
v___x_2086_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_2084_, v___x_2085_, v_d_2083_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_nested(lean_object* v_00_u03c4_2087_, lean_object* v_d_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Fmt_Doc_nested___redArg(v_d_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested___redArg(lean_object* v_d_2090_){
_start:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_unsigned_to_nat(2u);
v___x_2092_ = 1;
v___x_2093_ = l_Lean_Fmt_Doc_indented___override___redArg(v___x_2091_, v___x_2092_, v_d_2090_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_hardNested(lean_object* v_00_u03c4_2094_, lean_object* v_d_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Fmt_Doc_hardNested___redArg(v_d_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(lean_object* v_a_2097_, lean_object* v_b_2098_){
_start:
{
lean_object* v_array_2099_; lean_object* v_start_2100_; lean_object* v_stop_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2114_; 
v_array_2099_ = lean_ctor_get(v_a_2097_, 0);
v_start_2100_ = lean_ctor_get(v_a_2097_, 1);
v_stop_2101_ = lean_ctor_get(v_a_2097_, 2);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2103_ = v_a_2097_;
v_isShared_2104_ = v_isSharedCheck_2114_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_stop_2101_);
lean_inc(v_start_2100_);
lean_inc(v_array_2099_);
lean_dec(v_a_2097_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2114_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
uint8_t v___x_2105_; 
v___x_2105_ = lean_nat_dec_lt(v_start_2100_, v_stop_2101_);
if (v___x_2105_ == 0)
{
lean_del_object(v___x_2103_);
lean_dec(v_stop_2101_);
lean_dec(v_start_2100_);
lean_dec_ref(v_array_2099_);
return v_b_2098_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = lean_nat_add(v_start_2100_, v___x_2106_);
lean_inc_ref(v_array_2099_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 1, v___x_2107_);
v___x_2109_ = v___x_2103_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_array_2099_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_stop_2101_);
v___x_2109_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_array_fget(v_array_2099_, v_start_2100_);
lean_dec(v_start_2100_);
lean_dec_ref(v_array_2099_);
v___x_2111_ = l_Lean_Fmt_Doc_either___override___redArg(v_b_2098_, v___x_2110_);
v_a_2097_ = v___x_2109_;
v_b_2098_ = v___x_2111_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf___redArg(lean_object* v_ds_2115_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; uint8_t v___x_2118_; 
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = lean_array_get_size(v_ds_2115_);
v___x_2118_ = lean_nat_dec_lt(v___x_2116_, v___x_2117_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; 
lean_dec_ref(v_ds_2115_);
v___x_2119_ = lean_box(0);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2120_ = lean_array_fget(v_ds_2115_, v___x_2116_);
v___x_2121_ = lean_unsigned_to_nat(1u);
v___x_2122_ = l_Array_toSubarray___redArg(v_ds_2115_, v___x_2121_, v___x_2117_);
v___x_2123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v___x_2122_, v___x_2120_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_oneOf(lean_object* v_00_u03c4_2124_, lean_object* v_ds_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Fmt_Doc_oneOf___redArg(v_ds_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0(lean_object* v_00_u03c4_2127_, lean_object* v_inst_2128_, lean_object* v_R_2129_, lean_object* v_a_2130_, lean_object* v_b_2131_, lean_object* v_c_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_oneOf_spec__0___redArg(v_a_2130_, v_b_2131_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(lean_object* v_a_2134_, lean_object* v_b_2135_){
_start:
{
lean_object* v_array_2136_; lean_object* v_start_2137_; lean_object* v_stop_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2151_; 
v_array_2136_ = lean_ctor_get(v_a_2134_, 0);
v_start_2137_ = lean_ctor_get(v_a_2134_, 1);
v_stop_2138_ = lean_ctor_get(v_a_2134_, 2);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_a_2134_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2140_ = v_a_2134_;
v_isShared_2141_ = v_isSharedCheck_2151_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_stop_2138_);
lean_inc(v_start_2137_);
lean_inc(v_array_2136_);
lean_dec(v_a_2134_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2151_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_nat_dec_lt(v_start_2137_, v_stop_2138_);
if (v___x_2142_ == 0)
{
lean_del_object(v___x_2140_);
lean_dec(v_stop_2138_);
lean_dec(v_start_2137_);
lean_dec_ref(v_array_2136_);
return v_b_2135_;
}
else
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_add(v_start_2137_, v___x_2143_);
lean_inc_ref(v_array_2136_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 1, v___x_2144_);
v___x_2146_ = v___x_2140_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_array_2136_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2150_, 2, v_stop_2138_);
v___x_2146_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = lean_array_fget(v_array_2136_, v_start_2137_);
lean_dec(v_start_2137_);
lean_dec_ref(v_array_2136_);
v___x_2148_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_2135_, v___x_2147_);
v_a_2134_ = v___x_2146_;
v_b_2135_ = v___x_2148_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join___redArg(lean_object* v_ds_2152_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2153_ = lean_unsigned_to_nat(0u);
v___x_2154_ = lean_array_get_size(v_ds_2152_);
v___x_2155_ = lean_nat_dec_lt(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref(v_ds_2152_);
v___x_2156_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__1, &l_Lean_Fmt_Doc_empty___closed__1_once, _init_l_Lean_Fmt_Doc_empty___closed__1);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = lean_array_fget(v_ds_2152_, v___x_2153_);
v___x_2158_ = lean_unsigned_to_nat(1u);
v___x_2159_ = l_Array_toSubarray___redArg(v_ds_2152_, v___x_2158_, v___x_2154_);
v___x_2160_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v___x_2159_, v___x_2157_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_join(lean_object* v_00_u03c4_2161_, lean_object* v_ds_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Fmt_Doc_join___redArg(v_ds_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0(lean_object* v_00_u03c4_2164_, lean_object* v_inst_2165_, lean_object* v_R_2166_, lean_object* v_a_2167_, lean_object* v_b_2168_, lean_object* v_c_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_join_spec__0___redArg(v_a_2167_, v_b_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(lean_object* v_sep_2171_, lean_object* v_a_2172_, lean_object* v_b_2173_){
_start:
{
lean_object* v_array_2174_; lean_object* v_start_2175_; lean_object* v_stop_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2190_; 
v_array_2174_ = lean_ctor_get(v_a_2172_, 0);
v_start_2175_ = lean_ctor_get(v_a_2172_, 1);
v_stop_2176_ = lean_ctor_get(v_a_2172_, 2);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_a_2172_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2178_ = v_a_2172_;
v_isShared_2179_ = v_isSharedCheck_2190_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_stop_2176_);
lean_inc(v_start_2175_);
lean_inc(v_array_2174_);
lean_dec(v_a_2172_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2190_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_nat_dec_lt(v_start_2175_, v_stop_2176_);
if (v___x_2180_ == 0)
{
lean_del_object(v___x_2178_);
lean_dec(v_stop_2176_);
lean_dec(v_start_2175_);
lean_dec_ref(v_array_2174_);
lean_dec(v_sep_2171_);
return v_b_2173_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_nat_add(v_start_2175_, v___x_2181_);
lean_inc_ref(v_array_2174_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2182_);
v___x_2184_ = v___x_2178_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_array_2174_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_stop_2176_);
v___x_2184_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = lean_array_fget(v_array_2174_, v_start_2175_);
lean_dec(v_start_2175_);
lean_dec_ref(v_array_2174_);
lean_inc(v_sep_2171_);
v___x_2186_ = l_Lean_Fmt_Doc_append___override___redArg(v_b_2173_, v_sep_2171_);
v___x_2187_ = l_Lean_Fmt_Doc_append___override___redArg(v___x_2186_, v___x_2185_);
v_a_2172_ = v___x_2184_;
v_b_2173_ = v___x_2187_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing___redArg(lean_object* v_sep_2191_, lean_object* v_ds_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = lean_array_get_size(v_ds_2192_);
v___x_2195_ = lean_nat_dec_lt(v___x_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
lean_dec_ref(v_ds_2192_);
lean_dec(v_sep_2191_);
v___x_2196_ = lean_obj_once(&l_Lean_Fmt_Doc_empty___closed__1, &l_Lean_Fmt_Doc_empty___closed__1_once, _init_l_Lean_Fmt_Doc_empty___closed__1);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2197_ = lean_array_fget(v_ds_2192_, v___x_2193_);
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = l_Array_toSubarray___redArg(v_ds_2192_, v___x_2198_, v___x_2194_);
v___x_2200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_2191_, v___x_2199_, v___x_2197_);
return v___x_2200_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_joinUsing(lean_object* v_00_u03c4_2201_, lean_object* v_sep_2202_, lean_object* v_ds_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Fmt_Doc_joinUsing___redArg(v_sep_2202_, v_ds_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0(lean_object* v_00_u03c4_2205_, lean_object* v_sep_2206_, lean_object* v_inst_2207_, lean_object* v_R_2208_, lean_object* v_a_2209_, lean_object* v_b_2210_, lean_object* v_c_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_joinUsing_spec__0___redArg(v_sep_2206_, v_a_2209_, v_b_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Fmt_Doc_hardNl(lean_box(0));
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(lean_object* v_a_2214_, lean_object* v_b_2215_){
_start:
{
lean_object* v_array_2216_; lean_object* v_start_2217_; lean_object* v_stop_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2259_; 
v_array_2216_ = lean_ctor_get(v_a_2214_, 0);
v_start_2217_ = lean_ctor_get(v_a_2214_, 1);
v_stop_2218_ = lean_ctor_get(v_a_2214_, 2);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2220_ = v_a_2214_;
v_isShared_2221_ = v_isSharedCheck_2259_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_stop_2218_);
lean_inc(v_start_2217_);
lean_inc(v_array_2216_);
lean_dec(v_a_2214_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2259_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_nat_dec_lt(v_start_2217_, v_stop_2218_);
if (v___x_2222_ == 0)
{
lean_del_object(v___x_2220_);
lean_dec(v_stop_2218_);
lean_dec(v_start_2217_);
lean_dec_ref(v_array_2216_);
return v_b_2215_;
}
else
{
lean_object* v_fst_2223_; lean_object* v_snd_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2258_; 
v_fst_2223_ = lean_ctor_get(v_b_2215_, 0);
v_snd_2224_ = lean_ctor_get(v_b_2215_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_b_2215_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2226_ = v_b_2215_;
v_isShared_2227_ = v_isSharedCheck_2258_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_snd_2224_);
lean_inc(v_fst_2223_);
lean_dec(v_b_2215_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2258_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2228_ = lean_unsigned_to_nat(1u);
v___x_2229_ = lean_nat_add(v_start_2217_, v___x_2228_);
lean_inc_ref(v_array_2216_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 1, v___x_2229_);
v___x_2231_ = v___x_2220_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_array_2216_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_stop_2218_);
v___x_2231_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2232_ = lean_array_fget(v_array_2216_, v_start_2217_);
lean_dec(v_start_2217_);
lean_dec_ref(v_array_2216_);
v___x_2233_ = lean_unsigned_to_nat(2u);
v___x_2234_ = lean_mk_empty_array_with_capacity(v___x_2233_);
lean_inc_ref(v___x_2234_);
v___x_2235_ = lean_array_push(v___x_2234_, v_fst_2223_);
lean_inc_ref(v___x_2235_);
v___x_2236_ = lean_array_push(v___x_2235_, v_snd_2224_);
v___x_2237_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2236_);
lean_inc(v___x_2232_);
v___x_2238_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_2232_);
lean_inc(v___x_2238_);
v___x_2239_ = lean_array_push(v___x_2235_, v___x_2238_);
v___x_2240_ = l_Lean_Fmt_Doc_join___redArg(v___x_2239_);
v___x_2241_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2242_ = lean_unsigned_to_nat(3u);
v___x_2243_ = lean_mk_empty_array_with_capacity(v___x_2242_);
v___x_2244_ = lean_array_push(v___x_2243_, v___x_2237_);
v___x_2245_ = lean_array_push(v___x_2244_, v___x_2241_);
lean_inc_ref(v___x_2245_);
v___x_2246_ = lean_array_push(v___x_2245_, v___x_2238_);
v___x_2247_ = l_Lean_Fmt_Doc_join___redArg(v___x_2246_);
v___x_2248_ = lean_array_push(v___x_2234_, v___x_2240_);
v___x_2249_ = lean_array_push(v___x_2248_, v___x_2247_);
v___x_2250_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2249_);
v___x_2251_ = lean_array_push(v___x_2245_, v___x_2232_);
v___x_2252_ = l_Lean_Fmt_Doc_join___redArg(v___x_2251_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2252_);
lean_ctor_set(v___x_2226_, 0, v___x_2250_);
v___x_2254_ = v___x_2226_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
v_a_2214_ = v___x_2231_;
v_b_2215_ = v___x_2254_;
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
lean_object* v___x_2260_; 
v___x_2260_ = l_Lean_Fmt_Doc_empty(lean_box(0));
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill___redArg(lean_object* v_ds_2261_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2262_ = lean_array_get_size(v_ds_2261_);
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_nat_dec_eq(v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v_lastNotFlattened_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2265_ = lean_box(0);
v_lastNotFlattened_2266_ = lean_array_get(v___x_2265_, v_ds_2261_, v___x_2263_);
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_nat_dec_eq(v___x_2262_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v_lastFlattened_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v_fst_2273_; lean_object* v_snd_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_inc(v_lastNotFlattened_2266_);
v_lastFlattened_2269_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_2266_);
v___x_2270_ = l_Array_toSubarray___redArg(v_ds_2261_, v___x_2267_, v___x_2262_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_lastFlattened_2269_);
lean_ctor_set(v___x_2271_, 1, v_lastNotFlattened_2266_);
v___x_2272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(v___x_2270_, v___x_2271_);
v_fst_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_fst_2273_);
v_snd_2274_ = lean_ctor_get(v___x_2272_, 1);
lean_inc(v_snd_2274_);
lean_dec_ref(v___x_2272_);
v___x_2275_ = lean_unsigned_to_nat(2u);
v___x_2276_ = lean_mk_empty_array_with_capacity(v___x_2275_);
v___x_2277_ = lean_array_push(v___x_2276_, v_fst_2273_);
v___x_2278_ = lean_array_push(v___x_2277_, v_snd_2274_);
v___x_2279_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2278_);
return v___x_2279_;
}
else
{
lean_dec_ref(v_ds_2261_);
return v_lastNotFlattened_2266_;
}
}
else
{
lean_object* v___x_2280_; 
lean_dec_ref(v_ds_2261_);
v___x_2280_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fill(lean_object* v_00_u03c4_2281_, lean_object* v_ds_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Fmt_Doc_fill___redArg(v_ds_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0(lean_object* v_00_u03c4_2284_, lean_object* v_inst_2285_, lean_object* v_R_2286_, lean_object* v_a_2287_, lean_object* v_b_2288_, lean_object* v_c_2289_){
_start:
{
lean_object* v___x_2290_; 
v___x_2290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg(v_a_2287_, v_b_2288_);
return v___x_2290_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2291_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2292_ = lean_unsigned_to_nat(2u);
v___x_2293_ = lean_mk_empty_array_with_capacity(v___x_2292_);
v___x_2294_ = lean_array_push(v___x_2293_, v___x_2291_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(lean_object* v_wrap_2295_, lean_object* v_as_2296_, size_t v_sz_2297_, size_t v_i_2298_, lean_object* v_b_2299_){
_start:
{
uint8_t v___x_2300_; 
v___x_2300_ = lean_usize_dec_lt(v_i_2298_, v_sz_2297_);
if (v___x_2300_ == 0)
{
lean_dec_ref(v_wrap_2295_);
return v_b_2299_;
}
else
{
lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2335_; 
v_fst_2301_ = lean_ctor_get(v_b_2299_, 0);
v_snd_2302_ = lean_ctor_get(v_b_2299_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_b_2299_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2304_ = v_b_2299_;
v_isShared_2305_ = v_isSharedCheck_2335_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_snd_2302_);
lean_inc(v_fst_2301_);
lean_dec(v_b_2299_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2335_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v_a_2306_ = lean_array_uget_borrowed(v_as_2296_, v_i_2298_);
v___x_2307_ = lean_unsigned_to_nat(2u);
v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2307_);
lean_inc(v_fst_2301_);
lean_inc_ref_n(v___x_2308_, 3);
v___x_2309_ = lean_array_push(v___x_2308_, v_fst_2301_);
v___x_2310_ = lean_array_push(v___x_2309_, v_snd_2302_);
v___x_2311_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2310_);
v___x_2312_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_2313_ = lean_array_push(v___x_2312_, v___x_2311_);
v___x_2314_ = l_Lean_Fmt_Doc_join___redArg(v___x_2313_);
lean_inc_ref_n(v_wrap_2295_, 2);
v___x_2315_ = lean_apply_1(v_wrap_2295_, v___x_2314_);
lean_inc_n(v_a_2306_, 2);
v___x_2316_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_a_2306_);
v___x_2317_ = lean_apply_1(v_wrap_2295_, v_fst_2301_);
v___x_2318_ = lean_array_push(v___x_2308_, v___x_2316_);
lean_inc_ref(v___x_2318_);
v___x_2319_ = lean_array_push(v___x_2318_, v___x_2317_);
v___x_2320_ = l_Lean_Fmt_Doc_join___redArg(v___x_2319_);
lean_inc(v___x_2315_);
v___x_2321_ = lean_array_push(v___x_2318_, v___x_2315_);
v___x_2322_ = l_Lean_Fmt_Doc_join___redArg(v___x_2321_);
v___x_2323_ = lean_array_push(v___x_2308_, v___x_2320_);
v___x_2324_ = lean_array_push(v___x_2323_, v___x_2322_);
v___x_2325_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2324_);
v___x_2326_ = lean_array_push(v___x_2308_, v_a_2306_);
v___x_2327_ = lean_array_push(v___x_2326_, v___x_2315_);
v___x_2328_ = l_Lean_Fmt_Doc_join___redArg(v___x_2327_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2328_);
lean_ctor_set(v___x_2304_, 0, v___x_2325_);
v___x_2330_ = v___x_2304_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2325_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
size_t v___x_2331_; size_t v___x_2332_; 
v___x_2331_ = ((size_t)1ULL);
v___x_2332_ = lean_usize_add(v_i_2298_, v___x_2331_);
v_i_2298_ = v___x_2332_;
v_b_2299_ = v___x_2330_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___boxed(lean_object* v_wrap_2336_, lean_object* v_as_2337_, lean_object* v_sz_2338_, lean_object* v_i_2339_, lean_object* v_b_2340_){
_start:
{
size_t v_sz_boxed_2341_; size_t v_i_boxed_2342_; lean_object* v_res_2343_; 
v_sz_boxed_2341_ = lean_unbox_usize(v_sz_2338_);
lean_dec(v_sz_2338_);
v_i_boxed_2342_ = lean_unbox_usize(v_i_2339_);
lean_dec(v_i_2339_);
v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_2336_, v_as_2337_, v_sz_boxed_2341_, v_i_boxed_2342_, v_b_2340_);
lean_dec_ref(v_as_2337_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping___redArg(lean_object* v_ds_2344_, lean_object* v_wrap_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2346_ = lean_array_get_size(v_ds_2344_);
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_nat_dec_eq(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v_restNotFlattened_2352_; uint8_t v___x_2353_; 
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = lean_nat_sub(v___x_2346_, v___x_2350_);
v_restNotFlattened_2352_ = lean_array_get(v___x_2349_, v_ds_2344_, v___x_2351_);
lean_dec(v___x_2351_);
v___x_2353_ = lean_nat_dec_eq(v___x_2346_, v___x_2350_);
if (v___x_2353_ == 0)
{
lean_object* v_restFlattened_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; size_t v_sz_2358_; size_t v___x_2359_; lean_object* v___x_2360_; lean_object* v_fst_2361_; lean_object* v_snd_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_inc(v_restNotFlattened_2352_);
v_restFlattened_2354_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_2352_);
v___x_2355_ = lean_array_pop(v_ds_2344_);
v___x_2356_ = l_Array_reverse___redArg(v___x_2355_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v_restFlattened_2354_);
lean_ctor_set(v___x_2357_, 1, v_restNotFlattened_2352_);
v_sz_2358_ = lean_array_size(v___x_2356_);
v___x_2359_ = ((size_t)0ULL);
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_2345_, v___x_2356_, v_sz_2358_, v___x_2359_, v___x_2357_);
lean_dec_ref(v___x_2356_);
v_fst_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_fst_2361_);
v_snd_2362_ = lean_ctor_get(v___x_2360_, 1);
lean_inc(v_snd_2362_);
lean_dec_ref(v___x_2360_);
v___x_2363_ = lean_unsigned_to_nat(2u);
v___x_2364_ = lean_mk_empty_array_with_capacity(v___x_2363_);
v___x_2365_ = lean_array_push(v___x_2364_, v_fst_2361_);
v___x_2366_ = lean_array_push(v___x_2365_, v_snd_2362_);
v___x_2367_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2366_);
return v___x_2367_;
}
else
{
lean_dec_ref(v_wrap_2345_);
lean_dec_ref(v_ds_2344_);
return v_restNotFlattened_2352_;
}
}
else
{
lean_object* v___x_2368_; 
lean_dec_ref(v_wrap_2345_);
lean_dec_ref(v_ds_2344_);
v___x_2368_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillWrapping(lean_object* v_00_u03c4_2369_, lean_object* v_ds_2370_, lean_object* v_wrap_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Fmt_Doc_fillWrapping___redArg(v_ds_2370_, v_wrap_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0(lean_object* v_00_u03c4_2373_, lean_object* v_wrap_2374_, lean_object* v_as_2375_, size_t v_sz_2376_, size_t v_i_2377_, lean_object* v_b_2378_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg(v_wrap_2374_, v_as_2375_, v_sz_2376_, v_i_2377_, v_b_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___boxed(lean_object* v_00_u03c4_2380_, lean_object* v_wrap_2381_, lean_object* v_as_2382_, lean_object* v_sz_2383_, lean_object* v_i_2384_, lean_object* v_b_2385_){
_start:
{
size_t v_sz_boxed_2386_; size_t v_i_boxed_2387_; lean_object* v_res_2388_; 
v_sz_boxed_2386_ = lean_unbox_usize(v_sz_2383_);
lean_dec(v_sz_2383_);
v_i_boxed_2387_ = lean_unbox_usize(v_i_2384_);
lean_dec(v_i_2384_);
v_res_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0(v_00_u03c4_2380_, v_wrap_2381_, v_as_2382_, v_sz_boxed_2386_, v_i_boxed_2387_, v_b_2385_);
lean_dec_ref(v_as_2382_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(lean_object* v_sep_2389_, lean_object* v_a_2390_, lean_object* v_b_2391_){
_start:
{
lean_object* v_array_2392_; lean_object* v_start_2393_; lean_object* v_stop_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2440_; 
v_array_2392_ = lean_ctor_get(v_a_2390_, 0);
v_start_2393_ = lean_ctor_get(v_a_2390_, 1);
v_stop_2394_ = lean_ctor_get(v_a_2390_, 2);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_a_2390_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2396_ = v_a_2390_;
v_isShared_2397_ = v_isSharedCheck_2440_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_stop_2394_);
lean_inc(v_start_2393_);
lean_inc(v_array_2392_);
lean_dec(v_a_2390_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2440_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
uint8_t v___x_2398_; 
v___x_2398_ = lean_nat_dec_lt(v_start_2393_, v_stop_2394_);
if (v___x_2398_ == 0)
{
lean_del_object(v___x_2396_);
lean_dec(v_stop_2394_);
lean_dec(v_start_2393_);
lean_dec_ref(v_array_2392_);
lean_dec(v_sep_2389_);
return v_b_2391_;
}
else
{
lean_object* v_fst_2399_; lean_object* v_snd_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2439_; 
v_fst_2399_ = lean_ctor_get(v_b_2391_, 0);
v_snd_2400_ = lean_ctor_get(v_b_2391_, 1);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_b_2391_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2402_ = v_b_2391_;
v_isShared_2403_ = v_isSharedCheck_2439_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_snd_2400_);
lean_inc(v_fst_2399_);
lean_dec(v_b_2391_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2439_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_nat_add(v_start_2393_, v___x_2404_);
lean_inc_ref(v_array_2392_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 1, v___x_2405_);
v___x_2407_ = v___x_2396_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_array_2392_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_stop_2394_);
v___x_2407_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2408_ = lean_array_fget(v_array_2392_, v_start_2393_);
lean_dec(v_start_2393_);
lean_dec_ref(v_array_2392_);
v___x_2409_ = lean_unsigned_to_nat(2u);
v___x_2410_ = lean_mk_empty_array_with_capacity(v___x_2409_);
lean_inc(v_fst_2399_);
lean_inc_ref(v___x_2410_);
v___x_2411_ = lean_array_push(v___x_2410_, v_fst_2399_);
v___x_2412_ = lean_array_push(v___x_2411_, v_snd_2400_);
v___x_2413_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2412_);
lean_inc(v___x_2408_);
v___x_2414_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_2408_);
v___x_2415_ = lean_unsigned_to_nat(3u);
v___x_2416_ = lean_mk_empty_array_with_capacity(v___x_2415_);
v___x_2417_ = lean_array_push(v___x_2416_, v_fst_2399_);
lean_inc_n(v_sep_2389_, 2);
v___x_2418_ = lean_array_push(v___x_2417_, v_sep_2389_);
lean_inc(v___x_2414_);
v___x_2419_ = lean_array_push(v___x_2418_, v___x_2414_);
v___x_2420_ = l_Lean_Fmt_Doc_join___redArg(v___x_2419_);
v___x_2421_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2422_ = lean_unsigned_to_nat(4u);
v___x_2423_ = lean_mk_empty_array_with_capacity(v___x_2422_);
v___x_2424_ = lean_array_push(v___x_2423_, v___x_2413_);
v___x_2425_ = lean_array_push(v___x_2424_, v_sep_2389_);
v___x_2426_ = lean_array_push(v___x_2425_, v___x_2421_);
lean_inc_ref(v___x_2426_);
v___x_2427_ = lean_array_push(v___x_2426_, v___x_2414_);
v___x_2428_ = l_Lean_Fmt_Doc_join___redArg(v___x_2427_);
v___x_2429_ = lean_array_push(v___x_2410_, v___x_2420_);
v___x_2430_ = lean_array_push(v___x_2429_, v___x_2428_);
v___x_2431_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2430_);
v___x_2432_ = lean_array_push(v___x_2426_, v___x_2408_);
v___x_2433_ = l_Lean_Fmt_Doc_join___redArg(v___x_2432_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 1, v___x_2433_);
lean_ctor_set(v___x_2402_, 0, v___x_2431_);
v___x_2435_ = v___x_2402_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
v_a_2390_ = v___x_2407_;
v_b_2391_ = v___x_2435_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing___redArg(lean_object* v_sep_2441_, lean_object* v_ds_2442_){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; uint8_t v___x_2445_; 
v___x_2443_ = lean_array_get_size(v_ds_2442_);
v___x_2444_ = lean_unsigned_to_nat(0u);
v___x_2445_ = lean_nat_dec_eq(v___x_2443_, v___x_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v_lastNotFlattened_2447_; lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2446_ = lean_box(0);
v_lastNotFlattened_2447_ = lean_array_get(v___x_2446_, v_ds_2442_, v___x_2444_);
v___x_2448_ = lean_unsigned_to_nat(1u);
v___x_2449_ = lean_nat_dec_eq(v___x_2443_, v___x_2448_);
if (v___x_2449_ == 0)
{
lean_object* v_lastFlattened_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v_fst_2454_; lean_object* v_snd_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_inc(v_lastNotFlattened_2447_);
v_lastFlattened_2450_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_2447_);
v___x_2451_ = l_Array_toSubarray___redArg(v_ds_2442_, v___x_2448_, v___x_2443_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v_lastFlattened_2450_);
lean_ctor_set(v___x_2452_, 1, v_lastNotFlattened_2447_);
v___x_2453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(v_sep_2441_, v___x_2451_, v___x_2452_);
v_fst_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_fst_2454_);
v_snd_2455_ = lean_ctor_get(v___x_2453_, 1);
lean_inc(v_snd_2455_);
lean_dec_ref(v___x_2453_);
v___x_2456_ = lean_unsigned_to_nat(2u);
v___x_2457_ = lean_mk_empty_array_with_capacity(v___x_2456_);
v___x_2458_ = lean_array_push(v___x_2457_, v_fst_2454_);
v___x_2459_ = lean_array_push(v___x_2458_, v_snd_2455_);
v___x_2460_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2459_);
return v___x_2460_;
}
else
{
lean_dec_ref(v_ds_2442_);
lean_dec(v_sep_2441_);
return v_lastNotFlattened_2447_;
}
}
else
{
lean_object* v___x_2461_; 
lean_dec_ref(v_ds_2442_);
lean_dec(v_sep_2441_);
v___x_2461_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsing(lean_object* v_00_u03c4_2462_, lean_object* v_sep_2463_, lean_object* v_ds_2464_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_2463_, v_ds_2464_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0(lean_object* v_00_u03c4_2466_, lean_object* v_sep_2467_, lean_object* v_inst_2468_, lean_object* v_R_2469_, lean_object* v_a_2470_, lean_object* v_b_2471_, lean_object* v_c_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsing_spec__0___redArg(v_sep_2467_, v_a_2470_, v_b_2471_);
return v___x_2473_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = ((lean_object*)(l_Lean_Fmt_Doc_nl___closed__0));
v___x_2475_ = l_Lean_Fmt_Doc_text___override___redArg(v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(lean_object* v_a_2476_, lean_object* v_b_2477_){
_start:
{
lean_object* v_array_2478_; lean_object* v_start_2479_; lean_object* v_stop_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2524_; 
v_array_2478_ = lean_ctor_get(v_a_2476_, 0);
v_start_2479_ = lean_ctor_get(v_a_2476_, 1);
v_stop_2480_ = lean_ctor_get(v_a_2476_, 2);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2476_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2482_ = v_a_2476_;
v_isShared_2483_ = v_isSharedCheck_2524_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_stop_2480_);
lean_inc(v_start_2479_);
lean_inc(v_array_2478_);
lean_dec(v_a_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2524_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_nat_dec_lt(v_start_2479_, v_stop_2480_);
if (v___x_2484_ == 0)
{
lean_del_object(v___x_2482_);
lean_dec(v_stop_2480_);
lean_dec(v_start_2479_);
lean_dec_ref(v_array_2478_);
return v_b_2477_;
}
else
{
lean_object* v_fst_2485_; lean_object* v_snd_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2523_; 
v_fst_2485_ = lean_ctor_get(v_b_2477_, 0);
v_snd_2486_ = lean_ctor_get(v_b_2477_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_b_2477_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2488_ = v_b_2477_;
v_isShared_2489_ = v_isSharedCheck_2523_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_snd_2486_);
lean_inc(v_fst_2485_);
lean_dec(v_b_2477_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2523_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = lean_nat_add(v_start_2479_, v___x_2490_);
lean_inc_ref(v_array_2478_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2491_);
v___x_2493_ = v___x_2482_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_array_2478_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_stop_2480_);
v___x_2493_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2494_ = lean_array_fget(v_array_2478_, v_start_2479_);
lean_dec(v_start_2479_);
lean_dec_ref(v_array_2478_);
v___x_2495_ = lean_unsigned_to_nat(2u);
v___x_2496_ = lean_mk_empty_array_with_capacity(v___x_2495_);
lean_inc(v_fst_2485_);
lean_inc_ref(v___x_2496_);
v___x_2497_ = lean_array_push(v___x_2496_, v_fst_2485_);
v___x_2498_ = lean_array_push(v___x_2497_, v_snd_2486_);
v___x_2499_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2498_);
v___x_2500_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
lean_inc(v___x_2494_);
v___x_2501_ = l_Lean_Fmt_Doc_flattened___override___redArg(v___x_2494_);
v___x_2502_ = lean_unsigned_to_nat(3u);
v___x_2503_ = lean_mk_empty_array_with_capacity(v___x_2502_);
lean_inc_ref(v___x_2503_);
v___x_2504_ = lean_array_push(v___x_2503_, v_fst_2485_);
v___x_2505_ = lean_array_push(v___x_2504_, v___x_2500_);
lean_inc(v___x_2501_);
v___x_2506_ = lean_array_push(v___x_2505_, v___x_2501_);
v___x_2507_ = l_Lean_Fmt_Doc_join___redArg(v___x_2506_);
v___x_2508_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fill_spec__0___redArg___closed__0);
v___x_2509_ = lean_array_push(v___x_2503_, v___x_2499_);
v___x_2510_ = lean_array_push(v___x_2509_, v___x_2508_);
lean_inc_ref(v___x_2510_);
v___x_2511_ = lean_array_push(v___x_2510_, v___x_2501_);
v___x_2512_ = l_Lean_Fmt_Doc_join___redArg(v___x_2511_);
v___x_2513_ = lean_array_push(v___x_2496_, v___x_2507_);
v___x_2514_ = lean_array_push(v___x_2513_, v___x_2512_);
v___x_2515_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2514_);
v___x_2516_ = lean_array_push(v___x_2510_, v___x_2494_);
v___x_2517_ = l_Lean_Fmt_Doc_join___redArg(v___x_2516_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2517_);
lean_ctor_set(v___x_2488_, 0, v___x_2515_);
v___x_2519_ = v___x_2488_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
v_a_2476_ = v___x_2493_;
v_b_2477_ = v___x_2519_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace___redArg(lean_object* v_ds_2525_){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2526_ = lean_array_get_size(v_ds_2525_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_nat_dec_eq(v___x_2526_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v_lastNotFlattened_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2529_ = lean_box(0);
v_lastNotFlattened_2530_ = lean_array_get(v___x_2529_, v_ds_2525_, v___x_2527_);
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = lean_nat_dec_eq(v___x_2526_, v___x_2531_);
if (v___x_2532_ == 0)
{
lean_object* v_lastFlattened_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_fst_2537_; lean_object* v_snd_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_inc(v_lastNotFlattened_2530_);
v_lastFlattened_2533_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_lastNotFlattened_2530_);
v___x_2534_ = l_Array_toSubarray___redArg(v_ds_2525_, v___x_2531_, v___x_2526_);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v_lastFlattened_2533_);
lean_ctor_set(v___x_2535_, 1, v_lastNotFlattened_2530_);
v___x_2536_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(v___x_2534_, v___x_2535_);
v_fst_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_fst_2537_);
v_snd_2538_ = lean_ctor_get(v___x_2536_, 1);
lean_inc(v_snd_2538_);
lean_dec_ref(v___x_2536_);
v___x_2539_ = lean_unsigned_to_nat(2u);
v___x_2540_ = lean_mk_empty_array_with_capacity(v___x_2539_);
v___x_2541_ = lean_array_push(v___x_2540_, v_fst_2537_);
v___x_2542_ = lean_array_push(v___x_2541_, v_snd_2538_);
v___x_2543_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2542_);
return v___x_2543_;
}
else
{
lean_dec_ref(v_ds_2525_);
return v_lastNotFlattened_2530_;
}
}
else
{
lean_object* v___x_2544_; 
lean_dec_ref(v_ds_2525_);
v___x_2544_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpace(lean_object* v_00_u03c4_2545_, lean_object* v_ds_2546_){
_start:
{
lean_object* v___x_2547_; 
v___x_2547_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_ds_2546_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0(lean_object* v_00_u03c4_2548_, lean_object* v_inst_2549_, lean_object* v_R_2550_, lean_object* v_a_2551_, lean_object* v_b_2552_, lean_object* v_c_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg(v_a_2551_, v_b_2552_);
return v___x_2554_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2555_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Fmt_Doc_fillUsingSpace_spec__0___redArg___closed__0);
v___x_2556_ = lean_unsigned_to_nat(2u);
v___x_2557_ = lean_mk_empty_array_with_capacity(v___x_2556_);
v___x_2558_ = lean_array_push(v___x_2557_, v___x_2555_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(lean_object* v_wrap_2559_, lean_object* v_as_2560_, size_t v_sz_2561_, size_t v_i_2562_, lean_object* v_b_2563_){
_start:
{
uint8_t v___x_2564_; 
v___x_2564_ = lean_usize_dec_lt(v_i_2562_, v_sz_2561_);
if (v___x_2564_ == 0)
{
lean_dec_ref(v_wrap_2559_);
return v_b_2563_;
}
else
{
lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2602_; 
v_fst_2565_ = lean_ctor_get(v_b_2563_, 0);
v_snd_2566_ = lean_ctor_get(v_b_2563_, 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_b_2563_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2568_ = v_b_2563_;
v_isShared_2569_ = v_isSharedCheck_2602_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_dec(v_b_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2602_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_a_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v_a_2570_ = lean_array_uget_borrowed(v_as_2560_, v_i_2562_);
v___x_2571_ = lean_unsigned_to_nat(2u);
v___x_2572_ = lean_mk_empty_array_with_capacity(v___x_2571_);
lean_inc(v_fst_2565_);
lean_inc_ref_n(v___x_2572_, 3);
v___x_2573_ = lean_array_push(v___x_2572_, v_fst_2565_);
v___x_2574_ = lean_array_push(v___x_2573_, v_snd_2566_);
v___x_2575_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2574_);
v___x_2576_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_2577_ = lean_array_push(v___x_2576_, v___x_2575_);
v___x_2578_ = l_Lean_Fmt_Doc_join___redArg(v___x_2577_);
lean_inc_ref_n(v_wrap_2559_, 2);
v___x_2579_ = lean_apply_1(v_wrap_2559_, v___x_2578_);
lean_inc_n(v_a_2570_, 2);
v___x_2580_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_a_2570_);
v___x_2581_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_2582_ = lean_array_push(v___x_2581_, v_fst_2565_);
v___x_2583_ = l_Lean_Fmt_Doc_join___redArg(v___x_2582_);
v___x_2584_ = lean_apply_1(v_wrap_2559_, v___x_2583_);
v___x_2585_ = lean_array_push(v___x_2572_, v___x_2580_);
lean_inc_ref(v___x_2585_);
v___x_2586_ = lean_array_push(v___x_2585_, v___x_2584_);
v___x_2587_ = l_Lean_Fmt_Doc_join___redArg(v___x_2586_);
lean_inc(v___x_2579_);
v___x_2588_ = lean_array_push(v___x_2585_, v___x_2579_);
v___x_2589_ = l_Lean_Fmt_Doc_join___redArg(v___x_2588_);
v___x_2590_ = lean_array_push(v___x_2572_, v___x_2587_);
v___x_2591_ = lean_array_push(v___x_2590_, v___x_2589_);
v___x_2592_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2591_);
v___x_2593_ = lean_array_push(v___x_2572_, v_a_2570_);
v___x_2594_ = lean_array_push(v___x_2593_, v___x_2579_);
v___x_2595_ = l_Lean_Fmt_Doc_join___redArg(v___x_2594_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v___x_2595_);
lean_ctor_set(v___x_2568_, 0, v___x_2592_);
v___x_2597_ = v___x_2568_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
size_t v___x_2598_; size_t v___x_2599_; 
v___x_2598_ = ((size_t)1ULL);
v___x_2599_ = lean_usize_add(v_i_2562_, v___x_2598_);
v_i_2562_ = v___x_2599_;
v_b_2563_ = v___x_2597_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___boxed(lean_object* v_wrap_2603_, lean_object* v_as_2604_, lean_object* v_sz_2605_, lean_object* v_i_2606_, lean_object* v_b_2607_){
_start:
{
size_t v_sz_boxed_2608_; size_t v_i_boxed_2609_; lean_object* v_res_2610_; 
v_sz_boxed_2608_ = lean_unbox_usize(v_sz_2605_);
lean_dec(v_sz_2605_);
v_i_boxed_2609_ = lean_unbox_usize(v_i_2606_);
lean_dec(v_i_2606_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_2603_, v_as_2604_, v_sz_boxed_2608_, v_i_boxed_2609_, v_b_2607_);
lean_dec_ref(v_as_2604_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(lean_object* v_ds_2611_, lean_object* v_wrap_2612_){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; uint8_t v___x_2615_; 
v___x_2613_ = lean_array_get_size(v_ds_2611_);
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = lean_nat_dec_eq(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v_restNotFlattened_2619_; uint8_t v___x_2620_; 
v___x_2616_ = lean_box(0);
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = lean_nat_sub(v___x_2613_, v___x_2617_);
v_restNotFlattened_2619_ = lean_array_get(v___x_2616_, v_ds_2611_, v___x_2618_);
lean_dec(v___x_2618_);
v___x_2620_ = lean_nat_dec_eq(v___x_2613_, v___x_2617_);
if (v___x_2620_ == 0)
{
lean_object* v_restFlattened_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; size_t v_sz_2625_; size_t v___x_2626_; lean_object* v___x_2627_; lean_object* v_fst_2628_; lean_object* v_snd_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_inc(v_restNotFlattened_2619_);
v_restFlattened_2621_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_restNotFlattened_2619_);
v___x_2622_ = lean_array_pop(v_ds_2611_);
v___x_2623_ = l_Array_reverse___redArg(v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v_restFlattened_2621_);
lean_ctor_set(v___x_2624_, 1, v_restNotFlattened_2619_);
v_sz_2625_ = lean_array_size(v___x_2623_);
v___x_2626_ = ((size_t)0ULL);
v___x_2627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_2612_, v___x_2623_, v_sz_2625_, v___x_2626_, v___x_2624_);
lean_dec_ref(v___x_2623_);
v_fst_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_fst_2628_);
v_snd_2629_ = lean_ctor_get(v___x_2627_, 1);
lean_inc(v_snd_2629_);
lean_dec_ref(v___x_2627_);
v___x_2630_ = lean_unsigned_to_nat(2u);
v___x_2631_ = lean_mk_empty_array_with_capacity(v___x_2630_);
v___x_2632_ = lean_array_push(v___x_2631_, v_fst_2628_);
v___x_2633_ = lean_array_push(v___x_2632_, v_snd_2629_);
v___x_2634_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2633_);
return v___x_2634_;
}
else
{
lean_dec_ref(v_wrap_2612_);
lean_dec_ref(v_ds_2611_);
return v_restNotFlattened_2619_;
}
}
else
{
lean_object* v___x_2635_; 
lean_dec_ref(v_wrap_2612_);
lean_dec_ref(v_ds_2611_);
v___x_2635_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_2635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillUsingSpaceWrapping(lean_object* v_00_u03c4_2636_, lean_object* v_ds_2637_, lean_object* v_wrap_2638_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Fmt_Doc_fillUsingSpaceWrapping___redArg(v_ds_2637_, v_wrap_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0(lean_object* v_00_u03c4_2640_, lean_object* v_wrap_2641_, lean_object* v_as_2642_, size_t v_sz_2643_, size_t v_i_2644_, lean_object* v_b_2645_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg(v_wrap_2641_, v_as_2642_, v_sz_2643_, v_i_2644_, v_b_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___boxed(lean_object* v_00_u03c4_2647_, lean_object* v_wrap_2648_, lean_object* v_as_2649_, lean_object* v_sz_2650_, lean_object* v_i_2651_, lean_object* v_b_2652_){
_start:
{
size_t v_sz_boxed_2653_; size_t v_i_boxed_2654_; lean_object* v_res_2655_; 
v_sz_boxed_2653_ = lean_unbox_usize(v_sz_2650_);
lean_dec(v_sz_2650_);
v_i_boxed_2654_ = lean_unbox_usize(v_i_2651_);
lean_dec(v_i_2651_);
v_res_2655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0(v_00_u03c4_2647_, v_wrap_2648_, v_as_2649_, v_sz_boxed_2653_, v_i_boxed_2654_, v_b_2652_);
lean_dec_ref(v_as_2649_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default___redArg(lean_object* v_inst_2656_){
_start:
{
uint8_t v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = 0;
v___x_2658_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2658_, 0, v_inst_2656_);
lean_ctor_set_uint8(v___x_2658_, sizeof(void*)*1, v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable_default(lean_object* v_00_u03b1_2659_, lean_object* v_inst_2660_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable___redArg(lean_object* v_inst_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedFillable(lean_object* v_a_2664_, lean_object* v_inst_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v_inst_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(size_t v_sz_2667_, size_t v_i_2668_, lean_object* v_bs_2669_){
_start:
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_usize_dec_lt(v_i_2668_, v_sz_2667_);
if (v___x_2670_ == 0)
{
return v_bs_2669_;
}
else
{
lean_object* v_v_2671_; lean_object* v_v_2672_; lean_object* v___x_2673_; lean_object* v_bs_x27_2674_; size_t v___x_2675_; size_t v___x_2676_; lean_object* v___x_2677_; 
v_v_2671_ = lean_array_uget_borrowed(v_bs_2669_, v_i_2668_);
v_v_2672_ = lean_ctor_get(v_v_2671_, 0);
lean_inc(v_v_2672_);
v___x_2673_ = lean_unsigned_to_nat(0u);
v_bs_x27_2674_ = lean_array_uset(v_bs_2669_, v_i_2668_, v___x_2673_);
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = lean_usize_add(v_i_2668_, v___x_2675_);
v___x_2677_ = lean_array_uset(v_bs_x27_2674_, v_i_2668_, v_v_2672_);
v_i_2668_ = v___x_2676_;
v_bs_2669_ = v___x_2677_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg___boxed(lean_object* v_sz_2679_, lean_object* v_i_2680_, lean_object* v_bs_2681_){
_start:
{
size_t v_sz_boxed_2682_; size_t v_i_boxed_2683_; lean_object* v_res_2684_; 
v_sz_boxed_2682_ = lean_unbox_usize(v_sz_2679_);
lean_dec(v_sz_2679_);
v_i_boxed_2683_ = lean_unbox_usize(v_i_2680_);
lean_dec(v_i_2680_);
v_res_2684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_boxed_2682_, v_i_boxed_2683_, v_bs_2681_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(size_t v_sz_2685_, size_t v_i_2686_, lean_object* v_bs_2687_){
_start:
{
uint8_t v___x_2688_; 
v___x_2688_ = lean_usize_dec_lt(v_i_2686_, v_sz_2685_);
if (v___x_2688_ == 0)
{
return v_bs_2687_;
}
else
{
lean_object* v_v_2689_; lean_object* v___x_2690_; lean_object* v_bs_x27_2691_; size_t v_sz_2692_; size_t v___x_2693_; lean_object* v___x_2694_; size_t v___x_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v_v_2689_ = lean_array_uget(v_bs_2687_, v_i_2686_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v_bs_x27_2691_ = lean_array_uset(v_bs_2687_, v_i_2686_, v___x_2690_);
v_sz_2692_ = lean_array_size(v_v_2689_);
v___x_2693_ = ((size_t)0ULL);
v___x_2694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_2692_, v___x_2693_, v_v_2689_);
v___x_2695_ = ((size_t)1ULL);
v___x_2696_ = lean_usize_add(v_i_2686_, v___x_2695_);
v___x_2697_ = lean_array_uset(v_bs_x27_2691_, v_i_2686_, v___x_2694_);
v_i_2686_ = v___x_2696_;
v_bs_2687_ = v___x_2697_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg___boxed(lean_object* v_sz_2699_, lean_object* v_i_2700_, lean_object* v_bs_2701_){
_start:
{
size_t v_sz_boxed_2702_; size_t v_i_boxed_2703_; lean_object* v_res_2704_; 
v_sz_boxed_2702_ = lean_unbox_usize(v_sz_2699_);
lean_dec(v_sz_2699_);
v_i_boxed_2703_ = lean_unbox_usize(v_i_2700_);
lean_dec(v_i_2700_);
v_res_2704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_boxed_2702_, v_i_boxed_2703_, v_bs_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
if (lean_obj_tag(v_a_2705_) == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = l_List_reverse___redArg(v_a_2706_);
return v___x_2707_;
}
else
{
lean_object* v_head_2708_; lean_object* v_tail_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2718_; 
v_head_2708_ = lean_ctor_get(v_a_2705_, 0);
v_tail_2709_ = lean_ctor_get(v_a_2705_, 1);
v_isSharedCheck_2718_ = !lean_is_exclusive(v_a_2705_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2711_ = v_a_2705_;
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_tail_2709_);
lean_inc(v_head_2708_);
lean_dec(v_a_2705_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2718_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = lean_array_mk(v_head_2708_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_a_2706_);
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2715_ = v___x_2711_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2717_, 1, v_a_2706_);
v___x_2715_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
v_a_2705_ = v_tail_2709_;
v_a_2706_ = v___x_2715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
if (lean_obj_tag(v_a_2719_) == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_a_2720_);
lean_ctor_set(v___x_2723_, 1, v_a_2721_);
v___x_2724_ = l_List_reverse___redArg(v___x_2723_);
v___x_2725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_a_2722_);
v___x_2726_ = l_List_reverse___redArg(v___x_2725_);
return v___x_2726_;
}
else
{
lean_object* v_head_2727_; lean_object* v_tail_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2744_; 
v_head_2727_ = lean_ctor_get(v_a_2719_, 0);
v_tail_2728_ = lean_ctor_get(v_a_2719_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2730_ = v_a_2719_;
v_isShared_2731_ = v_isSharedCheck_2744_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_tail_2728_);
lean_inc(v_head_2727_);
lean_dec(v_a_2719_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2744_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
uint8_t v_allowFill_2740_; 
v_allowFill_2740_ = lean_ctor_get_uint8(v_a_2720_, sizeof(void*)*1);
if (v_allowFill_2740_ == 0)
{
goto v___jp_2732_;
}
else
{
uint8_t v_allowFill_2741_; 
v_allowFill_2741_ = lean_ctor_get_uint8(v_head_2727_, sizeof(void*)*1);
if (v_allowFill_2741_ == 0)
{
goto v___jp_2732_;
}
else
{
lean_object* v___x_2742_; 
lean_del_object(v___x_2730_);
v___x_2742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_a_2720_);
lean_ctor_set(v___x_2742_, 1, v_a_2721_);
v_a_2719_ = v_tail_2728_;
v_a_2720_ = v_head_2727_;
v_a_2721_ = v___x_2742_;
goto _start;
}
}
v___jp_2732_:
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = lean_box(0);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 1, v_a_2721_);
lean_ctor_set(v___x_2730_, 0, v_a_2720_);
v___x_2735_ = v___x_2730_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2720_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_a_2721_);
v___x_2735_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = l_List_reverse___redArg(v___x_2735_);
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v_a_2722_);
v_a_2719_ = v_tail_2728_;
v_a_2720_ = v_head_2727_;
v_a_2721_ = v___x_2733_;
v_a_2722_ = v___x_2737_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(lean_object* v_x_2745_){
_start:
{
if (lean_obj_tag(v_x_2745_) == 0)
{
lean_object* v___x_2746_; 
v___x_2746_ = lean_box(0);
return v___x_2746_;
}
else
{
lean_object* v_head_2747_; lean_object* v_tail_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_head_2747_ = lean_ctor_get(v_x_2745_, 0);
lean_inc(v_head_2747_);
v_tail_2748_ = lean_ctor_get(v_x_2745_, 1);
lean_inc(v_tail_2748_);
lean_dec_ref_known(v_x_2745_, 2);
v___x_2749_ = lean_box(0);
v___x_2750_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_tail_2748_, v_head_2747_, v___x_2749_, v___x_2749_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups___redArg(lean_object* v_ds_2751_){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v___x_2759_; 
v___x_2752_ = lean_array_to_list(v_ds_2751_);
v___x_2753_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v___x_2752_);
v___x_2754_ = lean_box(0);
v___x_2755_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v___x_2753_, v___x_2754_);
v___x_2756_ = lean_array_mk(v___x_2755_);
v_sz_2757_ = lean_array_size(v___x_2756_);
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_2757_, v___x_2758_, v___x_2756_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_splitFillGroups(lean_object* v_00_u03c4_2760_, lean_object* v_ds_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(lean_object* v_00_u03c4_2763_, size_t v_sz_2764_, size_t v_i_2765_, lean_object* v_bs_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___redArg(v_sz_2764_, v_i_2765_, v_bs_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0___boxed(lean_object* v_00_u03c4_2768_, lean_object* v_sz_2769_, lean_object* v_i_2770_, lean_object* v_bs_2771_){
_start:
{
size_t v_sz_boxed_2772_; size_t v_i_boxed_2773_; lean_object* v_res_2774_; 
v_sz_boxed_2772_ = lean_unbox_usize(v_sz_2769_);
lean_dec(v_sz_2769_);
v_i_boxed_2773_ = lean_unbox_usize(v_i_2770_);
lean_dec(v_i_2770_);
v_res_2774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__0(v_00_u03c4_2768_, v_sz_boxed_2772_, v_i_boxed_2773_, v_bs_2771_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1(lean_object* v_00_u03c4_2775_, lean_object* v_x_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l_List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1___redArg(v_x_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2(lean_object* v_00_u03c4_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_List_mapTR_loop___at___00Lean_Fmt_Doc_splitFillGroups_spec__2___redArg(v_a_2779_, v_a_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(lean_object* v_00_u03c4_2782_, size_t v_sz_2783_, size_t v_i_2784_, lean_object* v_bs_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___redArg(v_sz_2783_, v_i_2784_, v_bs_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3___boxed(lean_object* v_00_u03c4_2787_, lean_object* v_sz_2788_, lean_object* v_i_2789_, lean_object* v_bs_2790_){
_start:
{
size_t v_sz_boxed_2791_; size_t v_i_boxed_2792_; lean_object* v_res_2793_; 
v_sz_boxed_2791_ = lean_unbox_usize(v_sz_2788_);
lean_dec(v_sz_2788_);
v_i_boxed_2792_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_res_2793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_splitFillGroups_spec__3(v_00_u03c4_2787_, v_sz_boxed_2791_, v_i_boxed_2792_, v_bs_2790_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1(lean_object* v_00_u03c4_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_List_splitBy_loop___at___00List_splitBy___at___00Lean_Fmt_Doc_splitFillGroups_spec__1_spec__1___redArg(v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(lean_object* v_sep_2800_, size_t v_sz_2801_, size_t v_i_2802_, lean_object* v_bs_2803_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_usize_dec_lt(v_i_2802_, v_sz_2801_);
if (v___x_2804_ == 0)
{
lean_dec(v_sep_2800_);
return v_bs_2803_;
}
else
{
lean_object* v_v_2805_; lean_object* v___x_2806_; lean_object* v_bs_x27_2807_; lean_object* v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; lean_object* v___x_2811_; 
v_v_2805_ = lean_array_uget(v_bs_2803_, v_i_2802_);
v___x_2806_ = lean_unsigned_to_nat(0u);
v_bs_x27_2807_ = lean_array_uset(v_bs_2803_, v_i_2802_, v___x_2806_);
lean_inc(v_sep_2800_);
v___x_2808_ = l_Lean_Fmt_Doc_fillUsing___redArg(v_sep_2800_, v_v_2805_);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_add(v_i_2802_, v___x_2809_);
v___x_2811_ = lean_array_uset(v_bs_x27_2807_, v_i_2802_, v___x_2808_);
v_i_2802_ = v___x_2810_;
v_bs_2803_ = v___x_2811_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg___boxed(lean_object* v_sep_2813_, lean_object* v_sz_2814_, lean_object* v_i_2815_, lean_object* v_bs_2816_){
_start:
{
size_t v_sz_boxed_2817_; size_t v_i_boxed_2818_; lean_object* v_res_2819_; 
v_sz_boxed_2817_ = lean_unbox_usize(v_sz_2814_);
lean_dec(v_sz_2814_);
v_i_boxed_2818_ = lean_unbox_usize(v_i_2815_);
lean_dec(v_i_2815_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_2813_, v_sz_boxed_2817_, v_i_boxed_2818_, v_bs_2816_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing___redArg(lean_object* v_sep_2820_, lean_object* v_ds_2821_){
_start:
{
lean_object* v_fillGroups_2822_; lean_object* v___x_2823_; size_t v_sz_2824_; size_t v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_fillGroups_2822_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_2821_);
v___x_2823_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v_sz_2824_ = lean_array_size(v_fillGroups_2822_);
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_2820_, v_sz_2824_, v___x_2825_, v_fillGroups_2822_);
v___x_2827_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2823_, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsing(lean_object* v_00_u03c4_2828_, lean_object* v_sep_2829_, lean_object* v_ds_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_Fmt_Doc_fillSomeUsing___redArg(v_sep_2829_, v_ds_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0(lean_object* v_00_u03c4_2832_, lean_object* v_sep_2833_, size_t v_sz_2834_, size_t v_i_2835_, lean_object* v_bs_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___redArg(v_sep_2833_, v_sz_2834_, v_i_2835_, v_bs_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0___boxed(lean_object* v_00_u03c4_2838_, lean_object* v_sep_2839_, lean_object* v_sz_2840_, lean_object* v_i_2841_, lean_object* v_bs_2842_){
_start:
{
size_t v_sz_boxed_2843_; size_t v_i_boxed_2844_; lean_object* v_res_2845_; 
v_sz_boxed_2843_ = lean_unbox_usize(v_sz_2840_);
lean_dec(v_sz_2840_);
v_i_boxed_2844_ = lean_unbox_usize(v_i_2841_);
lean_dec(v_i_2841_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsing_spec__0(v_00_u03c4_2838_, v_sep_2839_, v_sz_boxed_2843_, v_i_boxed_2844_, v_bs_2842_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(size_t v_sz_2846_, size_t v_i_2847_, lean_object* v_bs_2848_){
_start:
{
uint8_t v___x_2849_; 
v___x_2849_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
if (v___x_2849_ == 0)
{
return v_bs_2848_;
}
else
{
lean_object* v_v_2850_; lean_object* v___x_2851_; lean_object* v_bs_x27_2852_; lean_object* v___x_2853_; size_t v___x_2854_; size_t v___x_2855_; lean_object* v___x_2856_; 
v_v_2850_ = lean_array_uget(v_bs_2848_, v_i_2847_);
v___x_2851_ = lean_unsigned_to_nat(0u);
v_bs_x27_2852_ = lean_array_uset(v_bs_2848_, v_i_2847_, v___x_2851_);
v___x_2853_ = l_Lean_Fmt_Doc_fillUsingSpace___redArg(v_v_2850_);
v___x_2854_ = ((size_t)1ULL);
v___x_2855_ = lean_usize_add(v_i_2847_, v___x_2854_);
v___x_2856_ = lean_array_uset(v_bs_x27_2852_, v_i_2847_, v___x_2853_);
v_i_2847_ = v___x_2855_;
v_bs_2848_ = v___x_2856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg___boxed(lean_object* v_sz_2858_, lean_object* v_i_2859_, lean_object* v_bs_2860_){
_start:
{
size_t v_sz_boxed_2861_; size_t v_i_boxed_2862_; lean_object* v_res_2863_; 
v_sz_boxed_2861_ = lean_unbox_usize(v_sz_2858_);
lean_dec(v_sz_2858_);
v_i_boxed_2862_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_boxed_2861_, v_i_boxed_2862_, v_bs_2860_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(lean_object* v_ds_2864_){
_start:
{
lean_object* v_fillGroups_2865_; lean_object* v___x_2866_; size_t v_sz_2867_; size_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_fillGroups_2865_ = l_Lean_Fmt_Doc_splitFillGroups___redArg(v_ds_2864_);
v___x_2866_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v_sz_2867_ = lean_array_size(v_fillGroups_2865_);
v___x_2868_ = ((size_t)0ULL);
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_2867_, v___x_2868_, v_fillGroups_2865_);
v___x_2870_ = l_Lean_Fmt_Doc_joinUsing___redArg(v___x_2866_, v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpace(lean_object* v_00_u03c4_2871_, lean_object* v_ds_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Fmt_Doc_fillSomeUsingSpace___redArg(v_ds_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(lean_object* v_00_u03c4_2874_, size_t v_sz_2875_, size_t v_i_2876_, lean_object* v_bs_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___redArg(v_sz_2875_, v_i_2876_, v_bs_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0___boxed(lean_object* v_00_u03c4_2879_, lean_object* v_sz_2880_, lean_object* v_i_2881_, lean_object* v_bs_2882_){
_start:
{
size_t v_sz_boxed_2883_; size_t v_i_boxed_2884_; lean_object* v_res_2885_; 
v_sz_boxed_2883_ = lean_unbox_usize(v_sz_2880_);
lean_dec(v_sz_2880_);
v_i_boxed_2884_ = lean_unbox_usize(v_i_2881_);
lean_dec(v_i_2881_);
v_res_2885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Fmt_Doc_fillSomeUsingSpace_spec__0(v_00_u03c4_2879_, v_sz_boxed_2883_, v_i_boxed_2884_, v_bs_2882_);
return v_res_2885_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2886_ = lean_obj_once(&l_Lean_Fmt_Doc_hardNl___closed__0, &l_Lean_Fmt_Doc_hardNl___closed__0_once, _init_l_Lean_Fmt_Doc_hardNl___closed__0);
v___x_2887_ = lean_unsigned_to_nat(2u);
v___x_2888_ = lean_mk_empty_array_with_capacity(v___x_2887_);
v___x_2889_ = lean_array_push(v___x_2888_, v___x_2886_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(lean_object* v_wrap_2890_, lean_object* v_as_2891_, size_t v_sz_2892_, size_t v_i_2893_, lean_object* v_b_2894_){
_start:
{
uint8_t v___x_2895_; 
v___x_2895_ = lean_usize_dec_lt(v_i_2893_, v_sz_2892_);
if (v___x_2895_ == 0)
{
lean_dec_ref(v_wrap_2890_);
return v_b_2894_;
}
else
{
lean_object* v_snd_2896_; lean_object* v_fst_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2963_; 
v_snd_2896_ = lean_ctor_get(v_b_2894_, 1);
v_fst_2897_ = lean_ctor_get(v_b_2894_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_b_2894_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2899_ = v_b_2894_;
v_isShared_2900_ = v_isSharedCheck_2963_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_snd_2896_);
lean_inc(v_fst_2897_);
lean_dec(v_b_2894_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2963_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v_fst_2901_; lean_object* v_snd_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2962_; 
v_fst_2901_ = lean_ctor_get(v_snd_2896_, 0);
v_snd_2902_ = lean_ctor_get(v_snd_2896_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_snd_2896_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2904_ = v_snd_2896_;
v_isShared_2905_ = v_isSharedCheck_2962_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snd_2902_);
lean_inc(v_fst_2901_);
lean_dec(v_snd_2896_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2962_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v_a_2906_; lean_object* v_restFlattened_2908_; lean_object* v_restNotFlattened_2909_; lean_object* v_v_2921_; uint8_t v_allowFill_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v_a_2906_ = lean_array_uget_borrowed(v_as_2891_, v_i_2893_);
v_v_2921_ = lean_ctor_get(v_a_2906_, 0);
v_allowFill_2922_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*1);
v___x_2923_ = lean_unsigned_to_nat(2u);
v___x_2924_ = lean_mk_empty_array_with_capacity(v___x_2923_);
lean_inc(v_fst_2897_);
lean_inc_ref(v___x_2924_);
v___x_2925_ = lean_array_push(v___x_2924_, v_fst_2897_);
v___x_2926_ = lean_array_push(v___x_2925_, v_fst_2901_);
v___x_2927_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2926_);
if (v_allowFill_2922_ == 0)
{
lean_dec(v_snd_2902_);
lean_dec(v_fst_2897_);
goto v___jp_2928_;
}
else
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_unbox(v_snd_2902_);
lean_dec(v_snd_2902_);
if (v___x_2941_ == 0)
{
lean_dec(v_fst_2897_);
goto v___jp_2928_;
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillWrapping_spec__0___redArg___closed__0);
v___x_2943_ = lean_array_push(v___x_2942_, v___x_2927_);
v___x_2944_ = l_Lean_Fmt_Doc_join___redArg(v___x_2943_);
lean_inc_ref_n(v_wrap_2890_, 2);
v___x_2945_ = lean_apply_1(v_wrap_2890_, v___x_2944_);
lean_inc_n(v_v_2921_, 2);
v___x_2946_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_2921_);
v___x_2947_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_2948_ = lean_array_push(v___x_2947_, v_fst_2897_);
v___x_2949_ = l_Lean_Fmt_Doc_join___redArg(v___x_2948_);
v___x_2950_ = lean_apply_1(v_wrap_2890_, v___x_2949_);
lean_inc_ref_n(v___x_2924_, 2);
v___x_2951_ = lean_array_push(v___x_2924_, v___x_2946_);
lean_inc_ref(v___x_2951_);
v___x_2952_ = lean_array_push(v___x_2951_, v___x_2950_);
v___x_2953_ = l_Lean_Fmt_Doc_join___redArg(v___x_2952_);
lean_inc(v___x_2945_);
v___x_2954_ = lean_array_push(v___x_2951_, v___x_2945_);
v___x_2955_ = l_Lean_Fmt_Doc_join___redArg(v___x_2954_);
v___x_2956_ = lean_array_push(v___x_2924_, v___x_2953_);
v___x_2957_ = lean_array_push(v___x_2956_, v___x_2955_);
v___x_2958_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_2957_);
v___x_2959_ = lean_array_push(v___x_2924_, v_v_2921_);
v___x_2960_ = lean_array_push(v___x_2959_, v___x_2945_);
v___x_2961_ = l_Lean_Fmt_Doc_join___redArg(v___x_2960_);
v_restFlattened_2908_ = v___x_2958_;
v_restNotFlattened_2909_ = v___x_2961_;
goto v___jp_2907_;
}
}
v___jp_2907_:
{
uint8_t v_allowFill_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v_allowFill_2910_ = lean_ctor_get_uint8(v_a_2906_, sizeof(void*)*1);
v___x_2911_ = lean_box(v_allowFill_2910_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 1, v___x_2911_);
lean_ctor_set(v___x_2904_, 0, v_restNotFlattened_2909_);
v___x_2913_ = v___x_2904_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_restNotFlattened_2909_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2915_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 1, v___x_2913_);
lean_ctor_set(v___x_2899_, 0, v_restFlattened_2908_);
v___x_2915_ = v___x_2899_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_restFlattened_2908_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
size_t v___x_2916_; size_t v___x_2917_; 
v___x_2916_ = ((size_t)1ULL);
v___x_2917_ = lean_usize_add(v_i_2893_, v___x_2916_);
v_i_2893_ = v___x_2917_;
v_b_2894_ = v___x_2915_;
goto _start;
}
}
}
v___jp_2928_:
{
lean_object* v_v_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_v_2929_ = lean_ctor_get(v_a_2906_, 0);
v___x_2930_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___closed__0);
v___x_2931_ = lean_array_push(v___x_2930_, v___x_2927_);
v___x_2932_ = l_Lean_Fmt_Doc_join___redArg(v___x_2931_);
lean_inc_ref(v_wrap_2890_);
v___x_2933_ = lean_apply_1(v_wrap_2890_, v___x_2932_);
lean_inc_n(v_v_2929_, 2);
v___x_2934_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_2929_);
lean_inc_ref(v___x_2924_);
v___x_2935_ = lean_array_push(v___x_2924_, v___x_2934_);
lean_inc(v___x_2933_);
v___x_2936_ = lean_array_push(v___x_2935_, v___x_2933_);
v___x_2937_ = l_Lean_Fmt_Doc_join___redArg(v___x_2936_);
v___x_2938_ = lean_array_push(v___x_2924_, v_v_2929_);
v___x_2939_ = lean_array_push(v___x_2938_, v___x_2933_);
v___x_2940_ = l_Lean_Fmt_Doc_join___redArg(v___x_2939_);
v_restFlattened_2908_ = v___x_2937_;
v_restNotFlattened_2909_ = v___x_2940_;
goto v___jp_2907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg___boxed(lean_object* v_wrap_2964_, lean_object* v_as_2965_, lean_object* v_sz_2966_, lean_object* v_i_2967_, lean_object* v_b_2968_){
_start:
{
size_t v_sz_boxed_2969_; size_t v_i_boxed_2970_; lean_object* v_res_2971_; 
v_sz_boxed_2969_ = lean_unbox_usize(v_sz_2966_);
lean_dec(v_sz_2966_);
v_i_boxed_2970_ = lean_unbox_usize(v_i_2967_);
lean_dec(v_i_2967_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_2964_, v_as_2965_, v_sz_boxed_2969_, v_i_boxed_2970_, v_b_2968_);
lean_dec_ref(v_as_2965_);
return v_res_2971_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_box(0);
v___x_2973_ = l_Lean_Fmt_instInhabitedFillable_default___redArg(v___x_2972_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(lean_object* v_ds_2974_, lean_object* v_wrap_2975_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2976_ = lean_array_get_size(v_ds_2974_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = lean_nat_dec_eq(v___x_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_last_2982_; uint8_t v___x_2983_; 
v___x_2979_ = lean_obj_once(&l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0, &l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg___closed__0);
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_sub(v___x_2976_, v___x_2980_);
v_last_2982_ = lean_array_get_borrowed(v___x_2979_, v_ds_2974_, v___x_2981_);
lean_dec(v___x_2981_);
v___x_2983_ = lean_nat_dec_eq(v___x_2976_, v___x_2980_);
if (v___x_2983_ == 0)
{
lean_object* v_v_2984_; uint8_t v_allowFill_2985_; lean_object* v_restFlattened_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; size_t v_sz_2992_; size_t v___x_2993_; lean_object* v___x_2994_; lean_object* v_snd_2995_; lean_object* v_fst_2996_; lean_object* v_fst_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_v_2984_ = lean_ctor_get(v_last_2982_, 0);
lean_inc_n(v_v_2984_, 2);
v_allowFill_2985_ = lean_ctor_get_uint8(v_last_2982_, sizeof(void*)*1);
v_restFlattened_2986_ = l_Lean_Fmt_Doc_flattened___override___redArg(v_v_2984_);
v___x_2987_ = lean_array_pop(v_ds_2974_);
v___x_2988_ = l_Array_reverse___redArg(v___x_2987_);
v___x_2989_ = lean_box(v_allowFill_2985_);
v___x_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2990_, 0, v_v_2984_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v_restFlattened_2986_);
lean_ctor_set(v___x_2991_, 1, v___x_2990_);
v_sz_2992_ = lean_array_size(v___x_2988_);
v___x_2993_ = ((size_t)0ULL);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_2975_, v___x_2988_, v_sz_2992_, v___x_2993_, v___x_2991_);
lean_dec_ref(v___x_2988_);
v_snd_2995_ = lean_ctor_get(v___x_2994_, 1);
lean_inc(v_snd_2995_);
v_fst_2996_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_fst_2996_);
lean_dec_ref(v___x_2994_);
v_fst_2997_ = lean_ctor_get(v_snd_2995_, 0);
lean_inc(v_fst_2997_);
lean_dec(v_snd_2995_);
v___x_2998_ = lean_unsigned_to_nat(2u);
v___x_2999_ = lean_mk_empty_array_with_capacity(v___x_2998_);
v___x_3000_ = lean_array_push(v___x_2999_, v_fst_2996_);
v___x_3001_ = lean_array_push(v___x_3000_, v_fst_2997_);
v___x_3002_ = l_Lean_Fmt_Doc_oneOf___redArg(v___x_3001_);
return v___x_3002_;
}
else
{
lean_object* v_v_3003_; 
lean_inc(v_last_2982_);
lean_dec_ref(v_wrap_2975_);
lean_dec_ref(v_ds_2974_);
v_v_3003_ = lean_ctor_get(v_last_2982_, 0);
lean_inc(v_v_3003_);
lean_dec(v_last_2982_);
return v_v_3003_;
}
}
else
{
lean_object* v___x_3004_; 
lean_dec_ref(v_wrap_2975_);
lean_dec_ref(v_ds_2974_);
v___x_3004_ = lean_obj_once(&l_Lean_Fmt_Doc_fill___redArg___closed__0, &l_Lean_Fmt_Doc_fill___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_fill___redArg___closed__0);
return v___x_3004_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping(lean_object* v_00_u03c4_3005_, lean_object* v_ds_3006_, lean_object* v_wrap_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_Fmt_Doc_fillSomeUsingSpaceWrapping___redArg(v_ds_3006_, v_wrap_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0(lean_object* v_00_u03c4_3009_, lean_object* v_wrap_3010_, lean_object* v_as_3011_, size_t v_sz_3012_, size_t v_i_3013_, lean_object* v_b_3014_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___redArg(v_wrap_3010_, v_as_3011_, v_sz_3012_, v_i_3013_, v_b_3014_);
return v___x_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0___boxed(lean_object* v_00_u03c4_3016_, lean_object* v_wrap_3017_, lean_object* v_as_3018_, lean_object* v_sz_3019_, lean_object* v_i_3020_, lean_object* v_b_3021_){
_start:
{
size_t v_sz_boxed_3022_; size_t v_i_boxed_3023_; lean_object* v_res_3024_; 
v_sz_boxed_3022_ = lean_unbox_usize(v_sz_3019_);
lean_dec(v_sz_3019_);
v_i_boxed_3023_ = lean_unbox_usize(v_i_3020_);
lean_dec(v_i_3020_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_Doc_fillSomeUsingSpaceWrapping_spec__0(v_00_u03c4_3016_, v_wrap_3017_, v_as_3018_, v_sz_boxed_3022_, v_i_boxed_3023_, v_b_3021_);
lean_dec_ref(v_as_3018_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instAppendDoc(lean_object* v_00_u03c4_3026_){
_start:
{
lean_object* v___f_3027_; 
v___f_3027_ = ((lean_object*)(l_Lean_Fmt_instAppendDoc___closed__0));
return v___f_3027_;
}
}
static size_t _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_3028_; size_t v___x_3029_; 
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = lean_usize_of_nat(v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default___redArg(lean_object* v_inst_3030_){
_start:
{
size_t v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_usize_once(&l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0, &l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0_once, _init_l_Lean_Fmt_instInhabitedPtrKey_default___redArg___closed__0);
v___x_3032_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_3032_, 0, v_inst_3030_);
lean_ctor_set_usize(v___x_3032_, 1, v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey_default(lean_object* v_00_u03b1_3033_, lean_object* v_inst_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey___redArg(lean_object* v_inst_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instInhabitedPtrKey(lean_object* v_a_3038_, lean_object* v_inst_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Fmt_instInhabitedPtrKey_default___redArg(v_inst_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey___redArg(lean_object* v_v_3041_){
_start:
{
size_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_ptr_addr(v_v_3041_);
v___x_3043_ = lean_alloc_ctor(0, 1, sizeof(size_t)*1);
lean_ctor_set(v___x_3043_, 0, v_v_3041_);
lean_ctor_set_usize(v___x_3043_, 1, v___x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_PtrKey_ofKey(lean_object* v_00_u03b1_3044_, lean_object* v_v_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_v_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqPtrKey___lam__0(lean_object* v_v1_3047_, lean_object* v_v2_3048_){
_start:
{
size_t v_ptr_3049_; size_t v_ptr_3050_; uint8_t v___x_3051_; 
v_ptr_3049_ = lean_ctor_get_usize(v_v1_3047_, 1);
v_ptr_3050_ = lean_ctor_get_usize(v_v2_3048_, 1);
v___x_3051_ = lean_usize_dec_eq(v_ptr_3049_, v_ptr_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey___lam__0___boxed(lean_object* v_v1_3052_, lean_object* v_v2_3053_){
_start:
{
uint8_t v_res_3054_; lean_object* v_r_3055_; 
v_res_3054_ = l_Lean_Fmt_instBEqPtrKey___lam__0(v_v1_3052_, v_v2_3053_);
lean_dec_ref(v_v2_3053_);
lean_dec_ref(v_v1_3052_);
v_r_3055_ = lean_box(v_res_3054_);
return v_r_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqPtrKey(lean_object* v_00_u03b1_3057_){
_start:
{
lean_object* v___f_3058_; 
v___f_3058_ = ((lean_object*)(l_Lean_Fmt_instBEqPtrKey___closed__0));
return v___f_3058_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashablePtrKey___lam__0(lean_object* v_v_3059_){
_start:
{
size_t v_ptr_3060_; uint64_t v___x_3061_; 
v_ptr_3060_ = lean_ctor_get_usize(v_v_3059_, 1);
v___x_3061_ = lean_usize_to_uint64(v_ptr_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey___lam__0___boxed(lean_object* v_v_3062_){
_start:
{
uint64_t v_res_3063_; lean_object* v_r_3064_; 
v_res_3063_ = l_Lean_Fmt_instHashablePtrKey___lam__0(v_v_3062_);
lean_dec_ref(v_v_3062_);
v_r_3064_ = lean_box_uint64(v_res_3063_);
return v_r_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashablePtrKey(lean_object* v_00_u03b1_3066_){
_start:
{
lean_object* v___f_3067_; 
v___f_3067_ = ((lean_object*)(l_Lean_Fmt_instHashablePtrKey___closed__0));
return v___f_3067_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
lean_object* v_aPtr_3070_; lean_object* v_aPtr_3071_; lean_object* v_bPtr_3072_; lean_object* v_bPtr_3073_; size_t v_ptr_3074_; size_t v_ptr_3075_; uint8_t v___x_3076_; 
v_aPtr_3070_ = lean_ctor_get(v_x_3068_, 0);
v_aPtr_3071_ = lean_ctor_get(v_x_3069_, 0);
v_bPtr_3072_ = lean_ctor_get(v_x_3068_, 1);
v_bPtr_3073_ = lean_ctor_get(v_x_3069_, 1);
v_ptr_3074_ = lean_ctor_get_usize(v_aPtr_3070_, 1);
v_ptr_3075_ = lean_ctor_get_usize(v_aPtr_3071_, 1);
v___x_3076_ = lean_usize_dec_eq(v_ptr_3074_, v_ptr_3075_);
if (v___x_3076_ == 0)
{
return v___x_3076_;
}
else
{
size_t v_ptr_3077_; size_t v_ptr_3078_; uint8_t v___x_3079_; 
v_ptr_3077_ = lean_ctor_get_usize(v_bPtr_3072_, 1);
v_ptr_3078_ = lean_ctor_get_usize(v_bPtr_3073_, 1);
v___x_3079_ = lean_usize_dec_eq(v_ptr_3077_, v_ptr_3078_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg___boxed(lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
uint8_t v_res_3082_; lean_object* v_r_3083_; 
v_res_3082_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_3080_, v_x_3081_);
lean_dec_ref(v_x_3081_);
lean_dec_ref(v_x_3080_);
v_r_3083_ = lean_box(v_res_3082_);
return v_r_3083_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqBEqCacheKey_beq(lean_object* v_00_u03c4_3084_, lean_object* v_inst_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_){
_start:
{
uint8_t v___x_3088_; 
v___x_3088_ = l_Lean_Fmt_instBEqBEqCacheKey_beq___redArg(v_x_3086_, v_x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed(lean_object* v_00_u03c4_3089_, lean_object* v_inst_3090_, lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
uint8_t v_res_3093_; lean_object* v_r_3094_; 
v_res_3093_ = l_Lean_Fmt_instBEqBEqCacheKey_beq(v_00_u03c4_3089_, v_inst_3090_, v_x_3091_, v_x_3092_);
lean_dec_ref(v_x_3092_);
lean_dec_ref(v_x_3091_);
lean_dec_ref(v_inst_3090_);
v_r_3094_ = lean_box(v_res_3093_);
return v_r_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey___redArg(lean_object* v_inst_3095_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_3096_, 0, lean_box(0));
lean_closure_set(v___x_3096_, 1, v_inst_3095_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqBEqCacheKey(lean_object* v_00_u03c4_3097_, lean_object* v_inst_3098_){
_start:
{
lean_object* v___x_3099_; 
v___x_3099_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_3099_, 0, lean_box(0));
lean_closure_set(v___x_3099_, 1, v_inst_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(lean_object* v_x_3100_){
_start:
{
lean_object* v_aPtr_3101_; lean_object* v_bPtr_3102_; size_t v_ptr_3103_; size_t v_ptr_3104_; uint64_t v___x_3105_; uint64_t v___x_3106_; uint64_t v___x_3107_; uint64_t v___x_3108_; uint64_t v___x_3109_; 
v_aPtr_3101_ = lean_ctor_get(v_x_3100_, 0);
v_bPtr_3102_ = lean_ctor_get(v_x_3100_, 1);
v_ptr_3103_ = lean_ctor_get_usize(v_aPtr_3101_, 1);
v_ptr_3104_ = lean_ctor_get_usize(v_bPtr_3102_, 1);
v___x_3105_ = 0ULL;
v___x_3106_ = lean_usize_to_uint64(v_ptr_3103_);
v___x_3107_ = lean_uint64_mix_hash(v___x_3105_, v___x_3106_);
v___x_3108_ = lean_usize_to_uint64(v_ptr_3104_);
v___x_3109_ = lean_uint64_mix_hash(v___x_3107_, v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg___boxed(lean_object* v_x_3110_){
_start:
{
uint64_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_3110_);
lean_dec_ref(v_x_3110_);
v_r_3112_ = lean_box_uint64(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT uint64_t l_Lean_Fmt_instHashableBEqCacheKey_hash(lean_object* v_00_u03c4_3113_, lean_object* v_inst_3114_, lean_object* v_x_3115_){
_start:
{
uint64_t v___x_3116_; 
v___x_3116_ = l_Lean_Fmt_instHashableBEqCacheKey_hash___redArg(v_x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed(lean_object* v_00_u03c4_3117_, lean_object* v_inst_3118_, lean_object* v_x_3119_){
_start:
{
uint64_t v_res_3120_; lean_object* v_r_3121_; 
v_res_3120_ = l_Lean_Fmt_instHashableBEqCacheKey_hash(v_00_u03c4_3117_, v_inst_3118_, v_x_3119_);
lean_dec_ref(v_x_3119_);
lean_dec_ref(v_inst_3118_);
v_r_3121_ = lean_box_uint64(v_res_3120_);
return v_r_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey___redArg(lean_object* v_inst_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_3123_, 0, lean_box(0));
lean_closure_set(v___x_3123_, 1, v_inst_3122_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instHashableBEqCacheKey(lean_object* v_00_u03c4_3124_, lean_object* v_inst_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_3126_, 0, lean_box(0));
lean_closure_set(v___x_3126_, 1, v_inst_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1___redArg(lean_object* v_a_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__1(lean_object* v_00_u03c4_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4___redArg(lean_object* v_b_3132_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3132_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized_unsafe__4(lean_object* v_00_u03c4_3134_, lean_object* v_b_3135_){
_start:
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_a_3139_, lean_object* v_b_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v___y_3147_; lean_object* v_da1_3152_; lean_object* v_da2_3153_; lean_object* v_db1_3154_; lean_object* v_db2_3155_; lean_object* v___y_3156_; lean_object* v_sa_3163_; lean_object* v_sb_3164_; lean_object* v___y_3165_; 
switch(lean_obj_tag(v_a_3139_))
{
case 0:
{
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
if (lean_obj_tag(v_b_3140_) == 0)
{
uint8_t v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = 1;
v___x_3170_ = lean_box(v___x_3169_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v_a_3141_);
return v___x_3171_;
}
else
{
lean_dec(v_b_3140_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 1:
{
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
if (lean_obj_tag(v_b_3140_) == 1)
{
lean_object* v_f_3172_; lean_object* v_f_3173_; 
v_f_3172_ = lean_ctor_get(v_a_3139_, 2);
lean_inc_ref(v_f_3172_);
lean_dec_ref_known(v_a_3139_, 3);
v_f_3173_ = lean_ctor_get(v_b_3140_, 2);
lean_inc_ref(v_f_3173_);
lean_dec_ref_known(v_b_3140_, 3);
v_sa_3163_ = v_f_3172_;
v_sb_3164_ = v_f_3173_;
v___y_3165_ = v_a_3141_;
goto v___jp_3162_;
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 2:
{
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
if (lean_obj_tag(v_b_3140_) == 2)
{
lean_object* v_s_3174_; lean_object* v_s_3175_; 
v_s_3174_ = lean_ctor_get(v_a_3139_, 2);
lean_inc_ref(v_s_3174_);
lean_dec_ref_known(v_a_3139_, 3);
v_s_3175_ = lean_ctor_get(v_b_3140_, 2);
lean_inc_ref(v_s_3175_);
lean_dec_ref_known(v_b_3140_, 3);
v_sa_3163_ = v_s_3174_;
v_sb_3164_ = v_s_3175_;
v___y_3165_ = v_a_3141_;
goto v___jp_3162_;
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 3:
{
if (lean_obj_tag(v_b_3140_) == 3)
{
lean_object* v_id_3176_; lean_object* v_d_3177_; lean_object* v_id_3178_; lean_object* v_d_3179_; uint8_t v___x_3180_; 
v_id_3176_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_id_3176_);
v_d_3177_ = lean_ctor_get(v_a_3139_, 3);
lean_inc(v_d_3177_);
lean_dec_ref_known(v_a_3139_, 4);
v_id_3178_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_id_3178_);
v_d_3179_ = lean_ctor_get(v_b_3140_, 3);
lean_inc(v_d_3179_);
lean_dec_ref_known(v_b_3140_, 4);
v___x_3180_ = lean_nat_dec_eq(v_id_3176_, v_id_3178_);
lean_dec(v_id_3178_);
lean_dec(v_id_3176_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v_d_3179_);
lean_dec(v_d_3177_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___x_3181_ = lean_box(v___x_3180_);
v___x_3182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v_a_3141_);
return v___x_3182_;
}
else
{
lean_object* v___x_3183_; 
v___x_3183_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3177_, v_d_3179_, v_a_3141_);
return v___x_3183_;
}
}
else
{
lean_dec_ref_known(v_a_3139_, 4);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 4:
{
if (lean_obj_tag(v_b_3140_) == 4)
{
lean_object* v_d_3184_; lean_object* v_d_3185_; lean_object* v___x_3186_; 
v_d_3184_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_d_3184_);
lean_dec_ref_known(v_a_3139_, 3);
v_d_3185_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_d_3185_);
lean_dec_ref_known(v_b_3140_, 3);
v___x_3186_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3184_, v_d_3185_, v_a_3141_);
return v___x_3186_;
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 5:
{
if (lean_obj_tag(v_b_3140_) == 5)
{
lean_object* v_d_3187_; lean_object* v_d_3188_; lean_object* v___x_3189_; 
v_d_3187_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_d_3187_);
lean_dec_ref_known(v_a_3139_, 3);
v_d_3188_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_d_3188_);
lean_dec_ref_known(v_b_3140_, 3);
v___x_3189_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3187_, v_d_3188_, v_a_3141_);
return v___x_3189_;
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 6:
{
if (lean_obj_tag(v_b_3140_) == 6)
{
lean_object* v_n_3190_; uint8_t v_isCumulative_3191_; lean_object* v_d_3192_; lean_object* v_n_3193_; uint8_t v_isCumulative_3194_; lean_object* v_d_3195_; uint8_t v___y_3197_; uint8_t v___x_3199_; 
v_n_3190_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_n_3190_);
v_isCumulative_3191_ = lean_ctor_get_uint8(v_a_3139_, sizeof(void*)*4 + 3);
v_d_3192_ = lean_ctor_get(v_a_3139_, 3);
lean_inc(v_d_3192_);
lean_dec_ref_known(v_a_3139_, 4);
v_n_3193_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_n_3193_);
v_isCumulative_3194_ = lean_ctor_get_uint8(v_b_3140_, sizeof(void*)*4 + 3);
v_d_3195_ = lean_ctor_get(v_b_3140_, 3);
lean_inc(v_d_3195_);
lean_dec_ref_known(v_b_3140_, 4);
v___x_3199_ = lean_nat_dec_eq(v_n_3190_, v_n_3193_);
lean_dec(v_n_3193_);
lean_dec(v_n_3190_);
if (v___x_3199_ == 0)
{
lean_dec(v_d_3195_);
lean_dec(v_d_3192_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
goto v___jp_3142_;
}
else
{
if (v_isCumulative_3191_ == 0)
{
if (v_isCumulative_3194_ == 0)
{
v___y_3197_ = v___x_3199_;
goto v___jp_3196_;
}
else
{
lean_dec(v_d_3195_);
lean_dec(v_d_3192_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
goto v___jp_3142_;
}
}
else
{
v___y_3197_ = v_isCumulative_3194_;
goto v___jp_3196_;
}
}
v___jp_3196_:
{
if (v___y_3197_ == 0)
{
lean_dec(v_d_3195_);
lean_dec(v_d_3192_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
goto v___jp_3142_;
}
else
{
lean_object* v___x_3198_; 
v___x_3198_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3192_, v_d_3195_, v_a_3141_);
return v___x_3198_;
}
}
}
else
{
lean_dec_ref_known(v_a_3139_, 4);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 7:
{
if (lean_obj_tag(v_b_3140_) == 7)
{
lean_object* v_d_3200_; lean_object* v_d_3201_; lean_object* v___x_3202_; 
v_d_3200_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_d_3200_);
lean_dec_ref_known(v_a_3139_, 3);
v_d_3201_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_d_3201_);
lean_dec_ref_known(v_b_3140_, 3);
v___x_3202_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3200_, v_d_3201_, v_a_3141_);
return v___x_3202_;
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 8:
{
if (lean_obj_tag(v_b_3140_) == 8)
{
uint8_t v_onlyNonCumulative_3203_; 
v_onlyNonCumulative_3203_ = lean_ctor_get_uint8(v_a_3139_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3203_ == 0)
{
uint8_t v_onlyNonCumulative_3204_; 
v_onlyNonCumulative_3204_ = lean_ctor_get_uint8(v_b_3140_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3204_ == 0)
{
lean_object* v_d_3205_; lean_object* v_d_3206_; lean_object* v___x_3207_; 
v_d_3205_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_d_3205_);
lean_dec_ref_known(v_a_3139_, 3);
v_d_3206_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_d_3206_);
lean_dec_ref_known(v_b_3140_, 3);
v___x_3207_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3205_, v_d_3206_, v_a_3141_);
return v___x_3207_;
}
else
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec_ref_known(v_b_3140_, 3);
lean_dec_ref_known(v_a_3139_, 3);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___x_3208_ = lean_box(v_onlyNonCumulative_3203_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v_a_3141_);
return v___x_3209_;
}
}
else
{
uint8_t v_onlyNonCumulative_3210_; 
v_onlyNonCumulative_3210_ = lean_ctor_get_uint8(v_b_3140_, sizeof(void*)*3 + 3);
if (v_onlyNonCumulative_3210_ == 0)
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
lean_dec_ref_known(v_b_3140_, 3);
lean_dec_ref_known(v_a_3139_, 3);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___x_3211_ = lean_box(v_onlyNonCumulative_3210_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v_a_3141_);
return v___x_3212_;
}
else
{
lean_object* v_d_3213_; lean_object* v_d_3214_; lean_object* v___x_3215_; 
v_d_3213_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_d_3213_);
lean_dec_ref_known(v_a_3139_, 3);
v_d_3214_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_d_3214_);
lean_dec_ref_known(v_b_3140_, 3);
v___x_3215_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3213_, v_d_3214_, v_a_3141_);
return v___x_3215_;
}
}
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 9:
{
if (lean_obj_tag(v_b_3140_) == 9)
{
lean_object* v_d_3216_; lean_object* v_d_3217_; lean_object* v___x_3218_; 
v_d_3216_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_d_3216_);
lean_dec_ref_known(v_a_3139_, 3);
v_d_3217_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_d_3217_);
lean_dec_ref_known(v_b_3140_, 3);
v___x_3218_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3216_, v_d_3217_, v_a_3141_);
return v___x_3218_;
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 10:
{
if (lean_obj_tag(v_b_3140_) == 10)
{
lean_object* v_d_3219_; lean_object* v_d_3220_; lean_object* v___x_3221_; 
v_d_3219_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_d_3219_);
lean_dec_ref_known(v_a_3139_, 3);
v_d_3220_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_d_3220_);
lean_dec_ref_known(v_b_3140_, 3);
v___x_3221_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3219_, v_d_3220_, v_a_3141_);
return v___x_3221_;
}
else
{
lean_dec_ref_known(v_a_3139_, 3);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 11:
{
if (lean_obj_tag(v_b_3140_) == 11)
{
lean_object* v_p_3222_; lean_object* v_p_3223_; lean_object* v_d_3224_; lean_object* v_d_3225_; lean_object* v_id_3226_; lean_object* v_id_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3237_; 
v_p_3222_ = lean_ctor_get(v_a_3139_, 2);
lean_inc_ref(v_p_3222_);
v_p_3223_ = lean_ctor_get(v_b_3140_, 2);
lean_inc_ref(v_p_3223_);
v_d_3224_ = lean_ctor_get(v_a_3139_, 3);
lean_inc(v_d_3224_);
lean_dec_ref_known(v_a_3139_, 4);
v_d_3225_ = lean_ctor_get(v_b_3140_, 3);
lean_inc(v_d_3225_);
lean_dec_ref_known(v_b_3140_, 4);
v_id_3226_ = lean_ctor_get(v_p_3222_, 1);
lean_inc(v_id_3226_);
lean_dec_ref(v_p_3222_);
v_id_3227_ = lean_ctor_get(v_p_3223_, 1);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_p_3223_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; 
v_unused_3238_ = lean_ctor_get(v_p_3223_, 0);
lean_dec(v_unused_3238_);
v___x_3229_ = v_p_3223_;
v_isShared_3230_ = v_isSharedCheck_3237_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_id_3227_);
lean_dec(v_p_3223_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3237_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
uint8_t v___x_3231_; 
v___x_3231_ = lean_name_eq(v_id_3226_, v_id_3227_);
lean_dec(v_id_3227_);
lean_dec(v_id_3226_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; lean_object* v___x_3234_; 
lean_dec(v_d_3225_);
lean_dec(v_d_3224_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___x_3232_ = lean_box(v___x_3231_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 1, v_a_3141_);
lean_ctor_set(v___x_3229_, 0, v___x_3232_);
v___x_3234_ = v___x_3229_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_a_3141_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
else
{
lean_object* v___x_3236_; 
lean_del_object(v___x_3229_);
v___x_3236_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3224_, v_d_3225_, v_a_3141_);
return v___x_3236_;
}
}
}
else
{
lean_dec_ref_known(v_a_3139_, 4);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 12:
{
if (lean_obj_tag(v_b_3140_) == 12)
{
lean_object* v_cost_3239_; lean_object* v_d_3240_; lean_object* v_cost_3241_; lean_object* v_d_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_cost_3239_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_cost_3239_);
v_d_3240_ = lean_ctor_get(v_a_3139_, 3);
lean_inc(v_d_3240_);
lean_dec_ref_known(v_a_3139_, 4);
v_cost_3241_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_cost_3241_);
v_d_3242_ = lean_ctor_get(v_b_3140_, 3);
lean_inc(v_d_3242_);
lean_dec_ref_known(v_b_3140_, 4);
lean_inc_ref(v_inst_3137_);
v___x_3243_ = lean_apply_2(v_inst_3137_, v_cost_3239_, v_cost_3241_);
v___x_3244_ = lean_unbox(v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; 
lean_dec(v_d_3242_);
lean_dec(v_d_3240_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v_a_3141_);
return v___x_3245_;
}
else
{
lean_object* v___x_3246_; 
v___x_3246_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_d_3240_, v_d_3242_, v_a_3141_);
return v___x_3246_;
}
}
else
{
lean_dec_ref_known(v_a_3139_, 4);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
case 13:
{
if (lean_obj_tag(v_b_3140_) == 13)
{
lean_object* v_a_3247_; lean_object* v_b_3248_; lean_object* v_a_3249_; lean_object* v_b_3250_; 
v_a_3247_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_a_3247_);
v_b_3248_ = lean_ctor_get(v_a_3139_, 3);
lean_inc(v_b_3248_);
lean_dec_ref_known(v_a_3139_, 4);
v_a_3249_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_a_3249_);
v_b_3250_ = lean_ctor_get(v_b_3140_, 3);
lean_inc(v_b_3250_);
lean_dec_ref_known(v_b_3140_, 4);
v_da1_3152_ = v_a_3247_;
v_da2_3153_ = v_b_3248_;
v_db1_3154_ = v_a_3249_;
v_db2_3155_ = v_b_3250_;
v___y_3156_ = v_a_3141_;
goto v___jp_3151_;
}
else
{
lean_dec_ref_known(v_a_3139_, 4);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
default: 
{
if (lean_obj_tag(v_b_3140_) == 14)
{
lean_object* v_a_3251_; lean_object* v_b_3252_; lean_object* v_a_3253_; lean_object* v_b_3254_; 
v_a_3251_ = lean_ctor_get(v_a_3139_, 2);
lean_inc(v_a_3251_);
v_b_3252_ = lean_ctor_get(v_a_3139_, 3);
lean_inc(v_b_3252_);
lean_dec_ref_known(v_a_3139_, 4);
v_a_3253_ = lean_ctor_get(v_b_3140_, 2);
lean_inc(v_a_3253_);
v_b_3254_ = lean_ctor_get(v_b_3140_, 3);
lean_inc(v_b_3254_);
lean_dec_ref_known(v_b_3140_, 4);
v_da1_3152_ = v_a_3251_;
v_da2_3153_ = v_b_3252_;
v_db1_3154_ = v_a_3253_;
v_db2_3155_ = v_b_3254_;
v___y_3156_ = v_a_3141_;
goto v___jp_3151_;
}
else
{
lean_dec_ref_known(v_a_3139_, 4);
lean_dec(v_b_3140_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
v___y_3147_ = v_a_3141_;
goto v___jp_3146_;
}
}
}
v___jp_3142_:
{
uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = 0;
v___x_3144_ = lean_box(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v_a_3141_);
return v___x_3145_;
}
v___jp_3146_:
{
uint8_t v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3148_ = 0;
v___x_3149_ = lean_box(v___x_3148_);
v___x_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v___y_3147_);
return v___x_3150_;
}
v___jp_3151_:
{
lean_object* v___x_3157_; lean_object* v_fst_3158_; uint8_t v___x_3159_; 
lean_inc_ref(v_inst_3138_);
lean_inc_ref(v_inst_3137_);
v___x_3157_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_da1_3152_, v_db1_3154_, v___y_3156_);
v_fst_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_fst_3158_);
v___x_3159_ = lean_unbox(v_fst_3158_);
lean_dec(v_fst_3158_);
if (v___x_3159_ == 0)
{
lean_dec(v_db2_3155_);
lean_dec(v_da2_3153_);
lean_dec_ref(v_inst_3138_);
lean_dec_ref(v_inst_3137_);
return v___x_3157_;
}
else
{
lean_object* v_snd_3160_; lean_object* v___x_3161_; 
v_snd_3160_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_snd_3160_);
lean_dec_ref(v___x_3157_);
v___x_3161_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3137_, v_inst_3138_, v_da2_3153_, v_db2_3155_, v_snd_3160_);
return v___x_3161_;
}
}
v___jp_3162_:
{
uint8_t v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = lean_string_dec_eq(v_sa_3163_, v_sb_3164_);
lean_dec_ref(v_sb_3164_);
lean_dec_ref(v_sa_3163_);
v___x_3167_ = lean_box(v___x_3166_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v___y_3165_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(lean_object* v_inst_3255_, lean_object* v_inst_3256_, lean_object* v_a_3257_, lean_object* v_b_3258_, lean_object* v_a_3259_){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v_cacheKey_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_inc(v_a_3257_);
v___x_3260_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_a_3257_);
lean_inc(v_b_3258_);
v___x_3261_ = l_Lean_Fmt_PtrKey_ofKey___redArg(v_b_3258_);
v_cacheKey_3262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_cacheKey_3262_, 0, v___x_3260_);
lean_ctor_set(v_cacheKey_3262_, 1, v___x_3261_);
lean_inc_ref(v_inst_3255_);
v___x_3263_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqBEqCacheKey_beq___boxed), 4, 2);
lean_closure_set(v___x_3263_, 0, lean_box(0));
lean_closure_set(v___x_3263_, 1, v_inst_3255_);
lean_inc_ref(v_inst_3256_);
v___x_3264_ = lean_alloc_closure((void*)(l_Lean_Fmt_instHashableBEqCacheKey_hash___boxed), 3, 2);
lean_closure_set(v___x_3264_, 0, lean_box(0));
lean_closure_set(v___x_3264_, 1, v_inst_3256_);
lean_inc_ref(v_cacheKey_3262_);
lean_inc_ref(v___x_3264_);
lean_inc_ref(v___x_3263_);
v___x_3265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_3263_, v___x_3264_, v_a_3259_, v_cacheKey_3262_);
if (lean_obj_tag(v___x_3265_) == 1)
{
lean_object* v_val_3266_; lean_object* v___x_3267_; 
lean_dec_ref(v___x_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref_known(v_cacheKey_3262_, 2);
lean_dec(v_b_3258_);
lean_dec(v_a_3257_);
lean_dec_ref(v_inst_3256_);
lean_dec_ref(v_inst_3255_);
v_val_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_val_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_val_3266_);
lean_ctor_set(v___x_3267_, 1, v_a_3259_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v_fst_3269_; lean_object* v_snd_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v___x_3265_);
v___x_3268_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_3255_, v_inst_3256_, v_a_3257_, v_b_3258_, v_a_3259_);
v_fst_3269_ = lean_ctor_get(v___x_3268_, 0);
v_snd_3270_ = lean_ctor_get(v___x_3268_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3272_ = v___x_3268_;
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_snd_3270_);
lean_inc(v_fst_3269_);
lean_dec(v___x_3268_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3278_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_inc(v_fst_3269_);
v___x_3274_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_3263_, v___x_3264_, v_snd_3270_, v_cacheKey_3262_, v_fst_3269_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 1, v___x_3274_);
v___x_3276_ = v___x_3272_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_fst_3269_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized(lean_object* v_00_u03c4_3279_, lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v_a_3282_, lean_object* v_b_3283_, lean_object* v_a_3284_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3280_, v_inst_3281_, v_a_3282_, v_b_3283_, v_a_3284_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go(lean_object* v_00_u03c4_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_a_3289_, lean_object* v_b_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3292_; 
v___x_3292_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_go___redArg(v_inst_3287_, v_inst_3288_, v_a_3289_, v_b_3290_, v_a_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_unsigned_to_nat(16u);
v___x_3295_ = lean_mk_array(v___x_3294_, v___x_3293_);
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_Fmt_Doc_beq___redArg___closed__1(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__0, &l_Lean_Fmt_Doc_beq___redArg___closed__0_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__0);
v___x_3297_ = lean_unsigned_to_nat(0u);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
lean_ctor_set(v___x_3298_, 1, v___x_3296_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___redArg(lean_object* v_inst_3299_, lean_object* v_inst_3300_, lean_object* v_a_3301_, lean_object* v_b_3302_){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v_fst_3305_; 
v___x_3303_ = lean_obj_once(&l_Lean_Fmt_Doc_beq___redArg___closed__1, &l_Lean_Fmt_Doc_beq___redArg___closed__1_once, _init_l_Lean_Fmt_Doc_beq___redArg___closed__1);
v___x_3304_ = l___private_Lean_Fmt_Core_Basic_0__Lean_Fmt_Doc_beq_goMemoized___redArg(v_inst_3299_, v_inst_3300_, v_a_3301_, v_b_3302_, v___x_3303_);
v_fst_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_fst_3305_);
lean_dec_ref(v___x_3304_);
return v_fst_3305_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_Doc_beq(lean_object* v_00_u03c4_3306_, lean_object* v_inst_3307_, lean_object* v_inst_3308_, lean_object* v_a_3309_, lean_object* v_b_3310_){
_start:
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_3307_, v_inst_3308_, v_a_3309_, v_b_3310_);
v___x_3312_ = lean_unbox(v___x_3311_);
lean_dec(v___x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_Doc_beq___boxed(lean_object* v_00_u03c4_3313_, lean_object* v_inst_3314_, lean_object* v_inst_3315_, lean_object* v_a_3316_, lean_object* v_b_3317_){
_start:
{
uint8_t v_res_3318_; lean_object* v_r_3319_; 
v_res_3318_ = l_Lean_Fmt_Doc_beq(v_00_u03c4_3313_, v_inst_3314_, v_inst_3315_, v_a_3316_, v_b_3317_);
v_r_3319_ = lean_box(v_res_3318_);
return v_r_3319_;
}
}
LEAN_EXPORT uint8_t l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_a_3322_, lean_object* v_b_3323_){
_start:
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = l_Lean_Fmt_Doc_beq___redArg(v_inst_3320_, v_inst_3321_, v_a_3322_, v_b_3323_);
v___x_3325_ = lean_unbox(v___x_3324_);
lean_dec(v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0___boxed(lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_a_3328_, lean_object* v_b_3329_){
_start:
{
uint8_t v_res_3330_; lean_object* v_r_3331_; 
v_res_3330_ = l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0(v_inst_3326_, v_inst_3327_, v_a_3328_, v_b_3329_);
v_r_3331_ = lean_box(v_res_3330_);
return v_r_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable___redArg(lean_object* v_inst_3332_, lean_object* v_inst_3333_){
_start:
{
lean_object* v___f_3334_; 
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3334_, 0, v_inst_3332_);
lean_closure_set(v___f_3334_, 1, v_inst_3333_);
return v___f_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_instBEqDocOfHashable(lean_object* v_00_u03c4_3335_, lean_object* v_inst_3336_, lean_object* v_inst_3337_){
_start:
{
lean_object* v___f_3338_; 
v___f_3338_ = lean_alloc_closure((void*)(l_Lean_Fmt_instBEqDocOfHashable___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_3338_, 0, v_inst_3336_);
lean_closure_set(v___f_3338_, 1, v_inst_3337_);
return v___f_3338_;
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

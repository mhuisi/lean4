// Lean compiler output
// Module: Lean.Syntax
// Imports: public import Init.Data.Slice public import Init.Data.Hashable public import Lean.Data.Format public import Init.Data.Option.Coe public import Init.Data.String.Hashable import Init.Data.Range.Polymorphic.Iterators import Init.Data.ToString.Macro import Init.Omega import Init.Syntax
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Substring_Raw_beq(lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_zipWith___at___00List_zip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Syntax_instInhabitedRange_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instInhabitedRange_default___closed__0 = (const lean_object*)&l_Lean_Syntax_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instInhabitedRange_default = (const lean_object*)&l_Lean_Syntax_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instInhabitedRange = (const lean_object*)&l_Lean_Syntax_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Syntax_instReprRange_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__7;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{ byteIdx := "};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__17;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__18;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instReprRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instReprRange_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instReprRange___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instReprRange = (const lean_object*)&l_Lean_Syntax_instReprRange___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEqRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqRange___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEqRange = (const lean_object*)&l_Lean_Syntax_instBEqRange___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instHashableRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instHashableRange_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instHashableRange___closed__0 = (const lean_object*)&l_Lean_Syntax_instHashableRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instHashableRange = (const lean_object*)&l_Lean_Syntax_instHashableRange___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqSourceInfo__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqSourceInfo__lean_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqSourceInfo__lean___closed__0 = (const lean_object*)&l_Lean_instBEqSourceInfo__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqSourceInfo__lean = (const lean_object*)&l_Lean_instBEqSourceInfo__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_isLitKind___closed__0 = (const lean_object*)&l_Lean_isLitKind___closed__0_value;
static const lean_ctor_object l_Lean_isLitKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_isLitKind___closed__1 = (const lean_object*)&l_Lean_isLitKind___closed__1_value;
static const lean_string_object l_Lean_isLitKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_isLitKind___closed__2 = (const lean_object*)&l_Lean_isLitKind___closed__2_value;
static const lean_ctor_object l_Lean_isLitKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_isLitKind___closed__3 = (const lean_object*)&l_Lean_isLitKind___closed__3_value;
static const lean_string_object l_Lean_isLitKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_isLitKind___closed__4 = (const lean_object*)&l_Lean_isLitKind___closed__4_value;
static const lean_ctor_object l_Lean_isLitKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_isLitKind___closed__5 = (const lean_object*)&l_Lean_isLitKind___closed__5_value;
static const lean_string_object l_Lean_isLitKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_isLitKind___closed__6 = (const lean_object*)&l_Lean_isLitKind___closed__6_value;
static const lean_ctor_object l_Lean_isLitKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_isLitKind___closed__7 = (const lean_object*)&l_Lean_isLitKind___closed__7_value;
static const lean_string_object l_Lean_isLitKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_isLitKind___closed__8 = (const lean_object*)&l_Lean_isLitKind___closed__8_value;
static const lean_ctor_object l_Lean_isLitKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__8_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_isLitKind___closed__9 = (const lean_object*)&l_Lean_isLitKind___closed__9_value;
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reuse stopped:\n"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " !=\n"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_0),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(46, 30, 230, 20, 64, 162, 204, 1)}};
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value_aux_1),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(32, 17, 142, 189, 192, 166, 31, 124)}};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_getAtomVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Syntax_getAtomVal___closed__0 = (const lean_object*)&l_Lean_Syntax_getAtomVal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_asNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_asNode___closed__0 = (const lean_object*)&l_Lean_Syntax_asNode___closed__0_value;
static const lean_string_object l_Lean_Syntax_asNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Syntax_asNode___closed__1 = (const lean_object*)&l_Lean_Syntax_asNode___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_asNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_asNode___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Syntax_asNode___closed__2 = (const lean_object*)&l_Lean_Syntax_asNode___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_asNode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Syntax_asNode___closed__2_value),((lean_object*)&l_Lean_Syntax_asNode___closed__0_value)}};
static const lean_object* l_Lean_Syntax_asNode___closed__3 = (const lean_object*)&l_Lean_Syntax_asNode___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__0 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__0_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__1 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__1_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__2 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__2_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__3 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__3_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__4 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__4_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__5 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__5_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__6 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_rewriteBottomUp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__0_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__1_value)}};
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__7 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__7_value;
static const lean_ctor_object l_Lean_Syntax_rewriteBottomUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__7_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__2_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__3_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__4_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__5_value)}};
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__8 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_rewriteBottomUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__8_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__6_value)}};
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__9 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0 = (const lean_object*)&l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_identComponents_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_identComponents_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_getAtomVal___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__1_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Syntax"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__2 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__2_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Syntax.identComponents\?"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__3 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__3_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__4 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__4_value;
static lean_once_cell_t l_Lean_Syntax_identComponents_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_identComponents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Syntax.identComponents"};
static const lean_object* l_Lean_Syntax_identComponents___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__0_value;
static lean_once_cell_t l_Lean_Syntax_identComponents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0 = (const lean_object*)&l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_Traverser_fromSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_Traverser_fromSyntax___closed__0 = (const lean_object*)&l_Lean_Syntax_Traverser_fromSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object*);
static const lean_string_object l_Lean_Syntax_isQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Syntax_isQuot___closed__0 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__0_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l_Lean_Syntax_isQuot___closed__1 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__1_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Syntax_isQuot___closed__2 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__2_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Syntax_isQuot___closed__3 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__3_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Syntax_isQuot___closed__4 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object*);
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value_aux_0),((lean_object*)&l_Lean_Syntax_isQuot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value_aux_1),((lean_object*)&l_Lean_Syntax_isQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value_aux_2),((lean_object*)&l_Lean_Syntax_isQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 123, 139, 164, 173, 191, 116, 242)}};
static const lean_object* l_Lean_Syntax_getQuotContent___closed__0 = (const lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
static const lean_string_object l_Lean_Syntax_isAntiquot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l_Lean_Syntax_isAntiquot___closed__0 = (const lean_object*)&l_Lean_Syntax_isAntiquot___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object*);
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__0 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__0_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__1;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isAntiquot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 141, 12, 45, 178, 67, 53, 106)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__2 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__2_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__3;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "pseudo"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__4 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 255, 48, 87, 29, 98, 48, 237)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__5 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__5_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__6 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__7 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__7_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__8 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__8_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__10;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__11 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__11_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_0),((lean_object*)&l_Lean_Syntax_isQuot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_1),((lean_object*)&l_Lean_Syntax_isQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_2),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__11_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__12 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "antiquotNestedExpr"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__13 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__13_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__13_value),LEAN_SCALAR_PTR_LITERAL(4, 217, 111, 200, 191, 162, 168, 125)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__14 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__14_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__15 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__15_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__16;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__17 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__17_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__18;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__19;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object*);
static const lean_string_object l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "antiquot_scope"};
static const lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "antiquot_splice"};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__0 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 54, 194, 194, 68, 126, 190, 193)}};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__1 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__1_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__2 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__2_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__3;
static const lean_string_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__4 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__4_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__5;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "antiquot_suffix_splice"};
static const lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object*);
static const lean_ctor_object l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 22, 214, 220, 194, 127, 23, 217)}};
static const lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_isTokenAntiquot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "token_antiquot"};
static const lean_object* l_Lean_Syntax_isTokenAntiquot___closed__0 = (const lean_object*)&l_Lean_Syntax_isTokenAntiquot___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isTokenAntiquot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isTokenAntiquot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 159, 231, 44, 235, 156, 55, 135)}};
static const lean_object* l_Lean_Syntax_isTokenAntiquot___closed__1 = (const lean_object*)&l_Lean_Syntax_isTokenAntiquot___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object*);
static const lean_array_object l_Lean_Syntax_Stack_matches___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_Stack_matches___closed__0 = (const lean_object*)&l_Lean_Syntax_Stack_matches___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Syntax_instReprRange_repr_spec__0(lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_nat_to_int(v_a_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(9u);
v___x_21_ = lean_nat_to_int(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(8u);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__0));
v___x_37_ = lean_string_length(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__17, &l_Lean_Syntax_instReprRange_repr___redArg___closed__17_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__17);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object* v_x_42_){
_start:
{
lean_object* v_start_43_; lean_object* v_stop_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_84_; 
v_start_43_ = lean_ctor_get(v_x_42_, 0);
v_stop_44_ = lean_ctor_get(v_x_42_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_84_ == 0)
{
v___x_46_ = v_x_42_;
v_isShared_47_ = v_isSharedCheck_84_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_stop_44_);
lean_inc(v_start_43_);
lean_dec(v_x_42_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_84_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_48_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__5));
v___x_49_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__6));
v___x_50_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__7, &l_Lean_Syntax_instReprRange_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__7);
v___x_51_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__9));
v___x_52_ = l_Nat_reprFast(v_start_43_);
v___x_53_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 5);
lean_ctor_set(v___x_46_, 1, v___x_53_);
lean_ctor_set(v___x_46_, 0, v___x_51_);
v___x_55_ = v___x_46_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_83_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_56_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__11));
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_50_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = 0;
v___x_60_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*1, v___x_59_);
v___x_61_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_49_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__13));
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = lean_box(1);
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__15));
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_48_);
v___x_69_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__16, &l_Lean_Syntax_instReprRange_repr___redArg___closed__16_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__16);
v___x_70_ = l_Nat_reprFast(v_stop_44_);
v___x_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_51_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_56_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_69_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_59_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_68_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__18, &l_Lean_Syntax_instReprRange_repr___redArg___closed__18_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__18);
v___x_78_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__19));
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_76_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_56_);
v___x_81_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_77_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_59_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr(lean_object* v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Syntax_instReprRange_repr___redArg(v_x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___boxed(lean_object* v_x_88_, lean_object* v_prec_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Syntax_instReprRange_repr(v_x_88_, v_prec_89_);
lean_dec(v_prec_89_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_start_95_; lean_object* v_stop_96_; lean_object* v_start_97_; lean_object* v_stop_98_; uint8_t v___x_99_; 
v_start_95_ = lean_ctor_get(v_x_93_, 0);
v_stop_96_ = lean_ctor_get(v_x_93_, 1);
v_start_97_ = lean_ctor_get(v_x_94_, 0);
v_stop_98_ = lean_ctor_get(v_x_94_, 1);
v___x_99_ = lean_nat_dec_eq(v_start_95_, v_start_97_);
if (v___x_99_ == 0)
{
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = lean_nat_dec_eq(v_stop_96_, v_stop_98_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_Syntax_instBEqRange_beq(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object* v_x_107_){
_start:
{
lean_object* v_start_108_; lean_object* v_stop_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; 
v_start_108_ = lean_ctor_get(v_x_107_, 0);
v_stop_109_ = lean_ctor_get(v_x_107_, 1);
v___x_110_ = 0ULL;
v___x_111_ = l_String_instHashableRaw_hash(v_start_108_);
v___x_112_ = lean_uint64_mix_hash(v___x_110_, v___x_111_);
v___x_113_ = l_String_instHashableRaw_hash(v_stop_109_);
v___x_114_ = lean_uint64_mix_hash(v___x_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object* v_x_115_){
_start:
{
uint64_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_Syntax_instHashableRange_hash(v_x_115_);
lean_dec_ref(v_x_115_);
v_r_117_ = lean_box_uint64(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_contains(lean_object* v_r_120_, lean_object* v_pos_121_, uint8_t v_includeStop_122_){
_start:
{
lean_object* v_start_123_; lean_object* v_stop_124_; uint8_t v___x_125_; 
v_start_123_ = lean_ctor_get(v_r_120_, 0);
v_stop_124_ = lean_ctor_get(v_r_120_, 1);
v___x_125_ = lean_nat_dec_le(v_start_123_, v_pos_121_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
if (v_includeStop_122_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_lt(v_pos_121_, v_stop_124_);
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_le(v_pos_121_, v_stop_124_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_contains___boxed(lean_object* v_r_128_, lean_object* v_pos_129_, lean_object* v_includeStop_130_){
_start:
{
uint8_t v_includeStop_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_includeStop_boxed_131_ = lean_unbox(v_includeStop_130_);
v_res_132_ = l_Lean_Syntax_Range_contains(v_r_128_, v_pos_129_, v_includeStop_boxed_131_);
lean_dec(v_pos_129_);
lean_dec_ref(v_r_128_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_includes(lean_object* v_super_134_, lean_object* v_sub_135_, uint8_t v_includeSuperStop_136_, uint8_t v_includeSubStop_137_){
_start:
{
lean_object* v_start_138_; lean_object* v_stop_139_; lean_object* v_start_140_; lean_object* v_stop_141_; uint8_t v___y_143_; uint8_t v___x_147_; uint8_t v___y_149_; 
v_start_138_ = lean_ctor_get(v_super_134_, 0);
v_stop_139_ = lean_ctor_get(v_super_134_, 1);
v_start_140_ = lean_ctor_get(v_sub_135_, 0);
v_stop_141_ = lean_ctor_get(v_sub_135_, 1);
v___x_147_ = lean_nat_dec_le(v_start_138_, v_start_140_);
if (v___x_147_ == 0)
{
return v___x_147_;
}
else
{
if (v_includeSuperStop_136_ == 0)
{
v___y_149_ = v_includeSuperStop_136_;
goto v___jp_148_;
}
else
{
if (v_includeSubStop_137_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_stop_139_, v___x_150_);
v___x_152_ = lean_nat_dec_le(v_stop_141_, v___x_151_);
lean_dec(v___x_151_);
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 0;
v___y_149_ = v___x_153_;
goto v___jp_148_;
}
}
}
v___jp_142_:
{
if (v___y_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_le(v_stop_141_, v_stop_139_);
return v___x_144_;
}
else
{
if (v_includeSubStop_137_ == 0)
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v_stop_141_, v_stop_139_);
return v___x_145_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_lt(v_stop_141_, v_stop_139_);
return v___x_146_;
}
}
}
v___jp_148_:
{
if (v_includeSuperStop_136_ == 0)
{
v___y_143_ = v___x_147_;
goto v___jp_142_;
}
else
{
v___y_143_ = v___y_149_;
goto v___jp_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object* v_super_154_, lean_object* v_sub_155_, lean_object* v_includeSuperStop_156_, lean_object* v_includeSubStop_157_){
_start:
{
uint8_t v_includeSuperStop_boxed_158_; uint8_t v_includeSubStop_boxed_159_; uint8_t v_res_160_; lean_object* v_r_161_; 
v_includeSuperStop_boxed_158_ = lean_unbox(v_includeSuperStop_156_);
v_includeSubStop_boxed_159_ = lean_unbox(v_includeSubStop_157_);
v_res_160_ = l_Lean_Syntax_Range_includes(v_super_154_, v_sub_155_, v_includeSuperStop_boxed_158_, v_includeSubStop_boxed_159_);
lean_dec_ref(v_sub_155_);
lean_dec_ref(v_super_154_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object* v_first_162_, lean_object* v_second_163_, uint8_t v_includeFirstStop_164_, uint8_t v_includeSecondStop_165_){
_start:
{
uint8_t v___y_167_; 
if (v_includeFirstStop_164_ == 0)
{
lean_object* v_start_174_; lean_object* v_stop_175_; uint8_t v___x_176_; 
v_start_174_ = lean_ctor_get(v_second_163_, 0);
v_stop_175_ = lean_ctor_get(v_first_162_, 1);
v___x_176_ = lean_nat_dec_lt(v_start_174_, v_stop_175_);
v___y_167_ = v___x_176_;
goto v___jp_166_;
}
else
{
lean_object* v_start_177_; lean_object* v_stop_178_; uint8_t v___x_179_; 
v_start_177_ = lean_ctor_get(v_second_163_, 0);
v_stop_178_ = lean_ctor_get(v_first_162_, 1);
v___x_179_ = lean_nat_dec_le(v_start_177_, v_stop_178_);
v___y_167_ = v___x_179_;
goto v___jp_166_;
}
v___jp_166_:
{
if (v___y_167_ == 0)
{
return v___y_167_;
}
else
{
if (v_includeSecondStop_165_ == 0)
{
lean_object* v_start_168_; lean_object* v_stop_169_; uint8_t v___x_170_; 
v_start_168_ = lean_ctor_get(v_first_162_, 0);
v_stop_169_ = lean_ctor_get(v_second_163_, 1);
v___x_170_ = lean_nat_dec_lt(v_start_168_, v_stop_169_);
return v___x_170_;
}
else
{
lean_object* v_start_171_; lean_object* v_stop_172_; uint8_t v___x_173_; 
v_start_171_ = lean_ctor_get(v_first_162_, 0);
v_stop_172_ = lean_ctor_get(v_second_163_, 1);
v___x_173_ = lean_nat_dec_le(v_start_171_, v_stop_172_);
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object* v_first_180_, lean_object* v_second_181_, lean_object* v_includeFirstStop_182_, lean_object* v_includeSecondStop_183_){
_start:
{
uint8_t v_includeFirstStop_boxed_184_; uint8_t v_includeSecondStop_boxed_185_; uint8_t v_res_186_; lean_object* v_r_187_; 
v_includeFirstStop_boxed_184_ = lean_unbox(v_includeFirstStop_182_);
v_includeSecondStop_boxed_185_ = lean_unbox(v_includeSecondStop_183_);
v_res_186_ = l_Lean_Syntax_Range_overlaps(v_first_180_, v_second_181_, v_includeFirstStop_boxed_184_, v_includeSecondStop_boxed_185_);
lean_dec_ref(v_second_181_);
lean_dec_ref(v_first_180_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object* v_r_188_){
_start:
{
lean_object* v_start_189_; lean_object* v_stop_190_; lean_object* v___x_191_; 
v_start_189_ = lean_ctor_get(v_r_188_, 0);
v_stop_190_ = lean_ctor_get(v_r_188_, 1);
v___x_191_ = lean_nat_sub(v_stop_190_, v_start_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object* v_r_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Syntax_Range_bsize(v_r_192_);
lean_dec_ref(v_r_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* v_trailing_194_, lean_object* v_x_195_){
_start:
{
if (lean_obj_tag(v_x_195_) == 0)
{
lean_object* v_leading_196_; lean_object* v_pos_197_; lean_object* v_endPos_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_leading_196_ = lean_ctor_get(v_x_195_, 0);
v_pos_197_ = lean_ctor_get(v_x_195_, 1);
v_endPos_198_ = lean_ctor_get(v_x_195_, 3);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_195_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_x_195_, 2);
lean_dec(v_unused_206_);
v___x_200_ = v_x_195_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_endPos_198_);
lean_inc(v_pos_197_);
lean_inc(v_leading_196_);
lean_dec(v_x_195_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 2, v_trailing_194_);
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_leading_196_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_pos_197_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_trailing_194_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_endPos_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_dec_ref(v_trailing_194_);
return v_x_195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t v_canonicalOnly_207_, lean_object* v_info_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_SourceInfo_getPos_x3f(v_info_208_, v_canonicalOnly_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_box(0);
return v___x_210_;
}
else
{
lean_object* v_val_211_; lean_object* v___x_212_; 
v_val_211_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_val_211_);
lean_dec_ref_known(v___x_209_, 1);
v___x_212_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_208_, v_canonicalOnly_207_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v___x_213_; 
lean_dec(v_val_211_);
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
v_val_214_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v___x_212_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_dec(v___x_212_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_val_211_);
lean_ctor_set(v___x_218_, 1, v_val_214_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object* v_canonicalOnly_223_, lean_object* v_info_224_){
_start:
{
uint8_t v_canonicalOnly_boxed_225_; lean_object* v_res_226_; 
v_canonicalOnly_boxed_225_ = lean_unbox(v_canonicalOnly_223_);
v_res_226_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_225_, v_info_224_);
lean_dec(v_info_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t v_canonicalOnly_227_, lean_object* v_info_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_SourceInfo_getPos_x3f(v_info_228_, v_canonicalOnly_227_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; 
v_val_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_229_, 1);
v___x_232_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_228_, v_canonicalOnly_227_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
lean_dec(v_val_231_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_242_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_242_ == 0)
{
v___x_236_ = v___x_232_;
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_val_234_);
lean_dec(v___x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_val_231_);
lean_ctor_set(v___x_238_, 1, v_val_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_238_);
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object* v_canonicalOnly_243_, lean_object* v_info_244_){
_start:
{
uint8_t v_canonicalOnly_boxed_245_; lean_object* v_res_246_; 
v_canonicalOnly_boxed_245_ = lean_unbox(v_canonicalOnly_243_);
v_res_246_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_245_, v_info_244_);
lean_dec(v_info_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object* v_x_247_){
_start:
{
switch(lean_obj_tag(v_x_247_))
{
case 0:
{
lean_object* v_pos_248_; lean_object* v_endPos_249_; uint8_t v___x_250_; lean_object* v___x_251_; 
v_pos_248_ = lean_ctor_get(v_x_247_, 1);
lean_inc(v_pos_248_);
v_endPos_249_ = lean_ctor_get(v_x_247_, 3);
lean_inc(v_endPos_249_);
lean_dec_ref_known(v_x_247_, 4);
v___x_250_ = 0;
v___x_251_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_251_, 0, v_pos_248_);
lean_ctor_set(v___x_251_, 1, v_endPos_249_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*2, v___x_250_);
return v___x_251_;
}
case 1:
{
lean_object* v_pos_252_; lean_object* v_endPos_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_pos_252_ = lean_ctor_get(v_x_247_, 0);
v_endPos_253_ = lean_ctor_get(v_x_247_, 1);
v_isSharedCheck_261_ = !lean_is_exclusive(v_x_247_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v_x_247_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_endPos_253_);
lean_inc(v_pos_252_);
lean_dec(v_x_247_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; lean_object* v___x_259_; 
v___x_257_ = 0;
if (v_isShared_256_ == 0)
{
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_pos_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_endPos_253_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*2, v___x_257_);
return v___x_259_;
}
}
}
default: 
{
return v_x_247_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
switch(lean_obj_tag(v_x_262_))
{
case 0:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_leading_264_; lean_object* v_pos_265_; lean_object* v_trailing_266_; lean_object* v_endPos_267_; lean_object* v_leading_268_; lean_object* v_pos_269_; lean_object* v_trailing_270_; lean_object* v_endPos_271_; uint8_t v___x_272_; 
v_leading_264_ = lean_ctor_get(v_x_262_, 0);
lean_inc_ref(v_leading_264_);
v_pos_265_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_pos_265_);
v_trailing_266_ = lean_ctor_get(v_x_262_, 2);
lean_inc_ref(v_trailing_266_);
v_endPos_267_ = lean_ctor_get(v_x_262_, 3);
lean_inc(v_endPos_267_);
lean_dec_ref_known(v_x_262_, 4);
v_leading_268_ = lean_ctor_get(v_x_263_, 0);
lean_inc_ref(v_leading_268_);
v_pos_269_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_pos_269_);
v_trailing_270_ = lean_ctor_get(v_x_263_, 2);
lean_inc_ref(v_trailing_270_);
v_endPos_271_ = lean_ctor_get(v_x_263_, 3);
lean_inc(v_endPos_271_);
lean_dec_ref_known(v_x_263_, 4);
v___x_272_ = l_Substring_Raw_beq(v_leading_264_, v_leading_268_);
if (v___x_272_ == 0)
{
lean_dec(v_endPos_271_);
lean_dec_ref(v_trailing_270_);
lean_dec(v_pos_269_);
lean_dec(v_endPos_267_);
lean_dec_ref(v_trailing_266_);
lean_dec(v_pos_265_);
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = lean_nat_dec_eq(v_pos_265_, v_pos_269_);
lean_dec(v_pos_269_);
lean_dec(v_pos_265_);
if (v___x_273_ == 0)
{
lean_dec(v_endPos_271_);
lean_dec_ref(v_trailing_270_);
lean_dec(v_endPos_267_);
lean_dec_ref(v_trailing_266_);
return v___x_273_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = l_Substring_Raw_beq(v_trailing_266_, v_trailing_270_);
if (v___x_274_ == 0)
{
lean_dec(v_endPos_271_);
lean_dec(v_endPos_267_);
return v___x_274_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_eq(v_endPos_267_, v_endPos_271_);
lean_dec(v_endPos_271_);
lean_dec(v_endPos_267_);
return v___x_275_;
}
}
}
}
else
{
uint8_t v___x_276_; 
lean_dec_ref_known(v_x_262_, 4);
lean_dec(v_x_263_);
v___x_276_ = 0;
return v___x_276_;
}
}
case 1:
{
if (lean_obj_tag(v_x_263_) == 1)
{
lean_object* v_pos_277_; lean_object* v_endPos_278_; uint8_t v_canonical_279_; lean_object* v_pos_280_; lean_object* v_endPos_281_; uint8_t v_canonical_282_; uint8_t v___x_283_; 
v_pos_277_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_pos_277_);
v_endPos_278_ = lean_ctor_get(v_x_262_, 1);
lean_inc(v_endPos_278_);
v_canonical_279_ = lean_ctor_get_uint8(v_x_262_, sizeof(void*)*2);
lean_dec_ref_known(v_x_262_, 2);
v_pos_280_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_pos_280_);
v_endPos_281_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_endPos_281_);
v_canonical_282_ = lean_ctor_get_uint8(v_x_263_, sizeof(void*)*2);
lean_dec_ref_known(v_x_263_, 2);
v___x_283_ = lean_nat_dec_eq(v_pos_277_, v_pos_280_);
lean_dec(v_pos_280_);
lean_dec(v_pos_277_);
if (v___x_283_ == 0)
{
lean_dec(v_endPos_281_);
lean_dec(v_endPos_278_);
return v___x_283_;
}
else
{
uint8_t v___x_284_; 
v___x_284_ = lean_nat_dec_eq(v_endPos_278_, v_endPos_281_);
lean_dec(v_endPos_281_);
lean_dec(v_endPos_278_);
if (v___x_284_ == 0)
{
return v___x_284_;
}
else
{
if (v_canonical_279_ == 0)
{
if (v_canonical_282_ == 0)
{
return v___x_284_;
}
else
{
return v_canonical_279_;
}
}
else
{
return v_canonical_282_;
}
}
}
}
else
{
uint8_t v___x_285_; 
lean_dec_ref_known(v_x_262_, 2);
lean_dec(v_x_263_);
v___x_285_ = 0;
return v___x_285_;
}
}
default: 
{
if (lean_obj_tag(v_x_263_) == 2)
{
uint8_t v___x_286_; 
v___x_286_ = 1;
return v___x_286_;
}
else
{
uint8_t v___x_287_; 
lean_dec(v_x_263_);
v___x_287_ = 0;
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_288_, v_x_289_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object* v_00_u03b2_294_, lean_object* v_a_295_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object* v_00_u03b2_296_, lean_object* v_info_297_, lean_object* v_val_298_, lean_object* v_a_299_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* v_00_u03b2_300_, lean_object* v_info_301_, lean_object* v_val_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_300_, v_info_301_, v_val_302_, v_a_303_);
lean_dec_ref(v_val_302_);
lean_dec(v_info_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object* v_00_u03b2_305_, lean_object* v_info_306_, lean_object* v_rawVal_307_, lean_object* v_val_308_, lean_object* v_preresolved_309_, lean_object* v_a_310_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* v_00_u03b2_311_, lean_object* v_info_312_, lean_object* v_rawVal_313_, lean_object* v_val_314_, lean_object* v_preresolved_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_unreachIsNodeIdent(v_00_u03b2_311_, v_info_312_, v_rawVal_313_, v_val_314_, v_preresolved_315_, v_a_316_);
lean_dec(v_preresolved_315_);
lean_dec(v_val_314_);
lean_dec_ref(v_rawVal_313_);
lean_dec(v_info_312_);
return v_res_317_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object* v_k_333_){
_start:
{
uint8_t v___y_335_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = ((lean_object*)(l_Lean_isLitKind___closed__7));
v___x_343_ = lean_name_eq(v_k_333_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_isLitKind___closed__9));
v___x_345_ = lean_name_eq(v_k_333_, v___x_344_);
v___y_335_ = v___x_345_;
goto v___jp_334_;
}
else
{
v___y_335_ = v___x_343_;
goto v___jp_334_;
}
v___jp_334_:
{
if (v___y_335_ == 0)
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = ((lean_object*)(l_Lean_isLitKind___closed__1));
v___x_337_ = lean_name_eq(v_k_333_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l_Lean_isLitKind___closed__3));
v___x_339_ = lean_name_eq(v_k_333_, v___x_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = ((lean_object*)(l_Lean_isLitKind___closed__5));
v___x_341_ = lean_name_eq(v_k_333_, v___x_340_);
return v___x_341_;
}
else
{
return v___x_339_;
}
}
else
{
return v___x_337_;
}
}
else
{
return v___y_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object* v_k_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Lean_isLitKind(v_k_346_);
lean_dec(v_k_346_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object* v_n_349_){
_start:
{
lean_object* v_kind_350_; 
v_kind_350_ = lean_ctor_get(v_n_349_, 1);
lean_inc(v_kind_350_);
return v_kind_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* v_n_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_SyntaxNode_getKind(v_n_351_);
lean_dec(v_n_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object* v_n_353_, lean_object* v_fn_354_){
_start:
{
lean_object* v_args_355_; lean_object* v___x_356_; 
v_args_355_ = lean_ctor_get(v_n_353_, 2);
lean_inc_ref(v_args_355_);
lean_dec(v_n_353_);
v___x_356_ = lean_apply_1(v_fn_354_, v_args_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object* v_00_u03b2_357_, lean_object* v_n_358_, lean_object* v_fn_359_){
_start:
{
lean_object* v_args_360_; lean_object* v___x_361_; 
v_args_360_ = lean_ctor_get(v_n_358_, 2);
lean_inc_ref(v_args_360_);
lean_dec(v_n_358_);
v___x_361_ = lean_apply_1(v_fn_359_, v_args_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* v_n_362_){
_start:
{
lean_object* v_args_363_; lean_object* v___x_364_; 
v_args_363_ = lean_ctor_get(v_n_362_, 2);
v___x_364_ = lean_array_get_size(v_args_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* v_n_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_SyntaxNode_getNumArgs(v_n_365_);
lean_dec(v_n_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object* v_n_367_, lean_object* v_i_368_){
_start:
{
lean_object* v_args_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v_args_369_ = lean_ctor_get(v_n_367_, 2);
v___x_370_ = lean_box(0);
v___x_371_ = lean_array_get_borrowed(v___x_370_, v_args_369_, v_i_368_);
lean_inc(v___x_371_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* v_n_372_, lean_object* v_i_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_SyntaxNode_getArg(v_n_372_, v_i_373_);
lean_dec(v_i_373_);
lean_dec(v_n_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object* v_n_375_){
_start:
{
lean_object* v_args_376_; 
v_args_376_ = lean_ctor_get(v_n_375_, 2);
lean_inc_ref(v_args_376_);
return v_args_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* v_n_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_SyntaxNode_getArgs(v_n_377_);
lean_dec(v_n_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* v_n_379_, lean_object* v_fn_380_){
_start:
{
lean_object* v_info_381_; lean_object* v_kind_382_; lean_object* v_args_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_391_; 
v_info_381_ = lean_ctor_get(v_n_379_, 0);
v_kind_382_ = lean_ctor_get(v_n_379_, 1);
v_args_383_ = lean_ctor_get(v_n_379_, 2);
v_isSharedCheck_391_ = !lean_is_exclusive(v_n_379_);
if (v_isSharedCheck_391_ == 0)
{
v___x_385_ = v_n_379_;
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_args_383_);
lean_inc(v_kind_382_);
lean_inc(v_info_381_);
lean_dec(v_n_379_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_391_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_apply_1(v_fn_380_, v_args_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 2, v___x_387_);
v___x_389_ = v___x_385_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_info_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_kind_382_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
if (lean_obj_tag(v_x_393_) == 0)
{
uint8_t v___x_394_; 
v___x_394_ = 1;
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = 0;
return v___x_395_;
}
}
else
{
if (lean_obj_tag(v_x_393_) == 0)
{
uint8_t v___x_396_; 
v___x_396_ = 0;
return v___x_396_;
}
else
{
lean_object* v_val_397_; lean_object* v_val_398_; uint8_t v___x_399_; 
v_val_397_ = lean_ctor_get(v_x_392_, 0);
v_val_398_ = lean_ctor_get(v_x_393_, 0);
v___x_399_ = l_Lean_Syntax_instBEqRange_beq(v_val_397_, v_val_398_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_400_, v_x_401_);
lean_dec(v_x_401_);
lean_dec(v_x_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
if (lean_obj_tag(v_x_405_) == 0)
{
uint8_t v___x_406_; 
v___x_406_ = 1;
return v___x_406_;
}
else
{
uint8_t v___x_407_; 
v___x_407_ = 0;
return v___x_407_;
}
}
else
{
if (lean_obj_tag(v_x_405_) == 0)
{
uint8_t v___x_408_; 
v___x_408_ = 0;
return v___x_408_;
}
else
{
lean_object* v_head_409_; lean_object* v_tail_410_; lean_object* v_head_411_; lean_object* v_tail_412_; uint8_t v___x_413_; 
v_head_409_ = lean_ctor_get(v_x_404_, 0);
v_tail_410_ = lean_ctor_get(v_x_404_, 1);
v_head_411_ = lean_ctor_get(v_x_405_, 0);
v_tail_412_ = lean_ctor_get(v_x_405_, 1);
v___x_413_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_409_, v_head_411_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
v_x_404_ = v_tail_410_;
v_x_405_ = v_tail_412_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_415_, v_x_416_);
lean_dec(v_x_416_);
lean_dec(v_x_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
switch(lean_obj_tag(v_x_419_))
{
case 0:
{
if (lean_obj_tag(v_x_420_) == 0)
{
uint8_t v___x_421_; 
v___x_421_ = 1;
return v___x_421_;
}
else
{
uint8_t v___x_422_; 
lean_dec(v_x_420_);
v___x_422_ = 0;
return v___x_422_;
}
}
case 1:
{
if (lean_obj_tag(v_x_420_) == 1)
{
lean_object* v_info_423_; lean_object* v_kind_424_; lean_object* v_args_425_; lean_object* v_info_426_; lean_object* v_kind_427_; lean_object* v_args_428_; uint8_t v___y_430_; uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_info_423_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_info_423_);
v_kind_424_ = lean_ctor_get(v_x_419_, 1);
lean_inc(v_kind_424_);
v_args_425_ = lean_ctor_get(v_x_419_, 2);
lean_inc_ref(v_args_425_);
lean_dec_ref_known(v_x_419_, 3);
v_info_426_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_info_426_);
v_kind_427_ = lean_ctor_get(v_x_420_, 1);
lean_inc(v_kind_427_);
v_args_428_ = lean_ctor_get(v_x_420_, 2);
lean_inc_ref(v_args_428_);
lean_dec_ref_known(v_x_420_, 3);
v___x_435_ = 0;
v___x_436_ = l_Lean_SourceInfo_getRange_x3f(v___x_435_, v_info_423_);
lean_dec(v_info_423_);
v___x_437_ = l_Lean_SourceInfo_getRange_x3f(v___x_435_, v_info_426_);
lean_dec(v_info_426_);
v___x_438_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_436_, v___x_437_);
lean_dec(v___x_437_);
lean_dec(v___x_436_);
if (v___x_438_ == 0)
{
lean_dec(v_kind_427_);
lean_dec(v_kind_424_);
v___y_430_ = v___x_438_;
goto v___jp_429_;
}
else
{
uint8_t v___x_439_; 
v___x_439_ = lean_name_eq(v_kind_424_, v_kind_427_);
lean_dec(v_kind_427_);
lean_dec(v_kind_424_);
v___y_430_ = v___x_439_;
goto v___jp_429_;
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
lean_dec_ref(v_args_428_);
lean_dec_ref(v_args_425_);
return v___y_430_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_array_get_size(v_args_425_);
v___x_432_ = lean_array_get_size(v_args_428_);
v___x_433_ = lean_nat_dec_eq(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec_ref(v_args_428_);
lean_dec_ref(v_args_425_);
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_args_425_, v_args_428_, v___x_431_);
lean_dec_ref(v_args_428_);
lean_dec_ref(v_args_425_);
return v___x_434_;
}
}
}
}
else
{
uint8_t v___x_440_; 
lean_dec_ref_known(v_x_419_, 3);
lean_dec(v_x_420_);
v___x_440_ = 0;
return v___x_440_;
}
}
case 2:
{
if (lean_obj_tag(v_x_420_) == 2)
{
lean_object* v_info_441_; lean_object* v_val_442_; lean_object* v_info_443_; lean_object* v_val_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_info_441_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_info_441_);
v_val_442_ = lean_ctor_get(v_x_419_, 1);
lean_inc_ref(v_val_442_);
lean_dec_ref_known(v_x_419_, 2);
v_info_443_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_info_443_);
v_val_444_ = lean_ctor_get(v_x_420_, 1);
lean_inc_ref(v_val_444_);
lean_dec_ref_known(v_x_420_, 2);
v___x_445_ = 0;
v___x_446_ = l_Lean_SourceInfo_getRange_x3f(v___x_445_, v_info_441_);
lean_dec(v_info_441_);
v___x_447_ = l_Lean_SourceInfo_getRange_x3f(v___x_445_, v_info_443_);
lean_dec(v_info_443_);
v___x_448_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_446_, v___x_447_);
lean_dec(v___x_447_);
lean_dec(v___x_446_);
if (v___x_448_ == 0)
{
lean_dec_ref(v_val_444_);
lean_dec_ref(v_val_442_);
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
v___x_449_ = lean_string_dec_eq(v_val_442_, v_val_444_);
lean_dec_ref(v_val_444_);
lean_dec_ref(v_val_442_);
return v___x_449_;
}
}
else
{
uint8_t v___x_450_; 
lean_dec_ref_known(v_x_419_, 2);
lean_dec(v_x_420_);
v___x_450_ = 0;
return v___x_450_;
}
}
default: 
{
if (lean_obj_tag(v_x_420_) == 3)
{
lean_object* v_info_451_; lean_object* v_rawVal_452_; lean_object* v_val_453_; lean_object* v_preresolved_454_; lean_object* v_info_455_; lean_object* v_rawVal_456_; lean_object* v_val_457_; lean_object* v_preresolved_458_; uint8_t v___y_460_; uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_info_451_ = lean_ctor_get(v_x_419_, 0);
lean_inc(v_info_451_);
v_rawVal_452_ = lean_ctor_get(v_x_419_, 1);
lean_inc_ref(v_rawVal_452_);
v_val_453_ = lean_ctor_get(v_x_419_, 2);
lean_inc(v_val_453_);
v_preresolved_454_ = lean_ctor_get(v_x_419_, 3);
lean_inc(v_preresolved_454_);
lean_dec_ref_known(v_x_419_, 4);
v_info_455_ = lean_ctor_get(v_x_420_, 0);
lean_inc(v_info_455_);
v_rawVal_456_ = lean_ctor_get(v_x_420_, 1);
lean_inc_ref(v_rawVal_456_);
v_val_457_ = lean_ctor_get(v_x_420_, 2);
lean_inc(v_val_457_);
v_preresolved_458_ = lean_ctor_get(v_x_420_, 3);
lean_inc(v_preresolved_458_);
lean_dec_ref_known(v_x_420_, 4);
v___x_463_ = 0;
v___x_464_ = l_Lean_SourceInfo_getRange_x3f(v___x_463_, v_info_451_);
lean_dec(v_info_451_);
v___x_465_ = l_Lean_SourceInfo_getRange_x3f(v___x_463_, v_info_455_);
lean_dec(v_info_455_);
v___x_466_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_464_, v___x_465_);
lean_dec(v___x_465_);
lean_dec(v___x_464_);
if (v___x_466_ == 0)
{
lean_dec_ref(v_rawVal_456_);
lean_dec_ref(v_rawVal_452_);
v___y_460_ = v___x_466_;
goto v___jp_459_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = l_Substring_Raw_beq(v_rawVal_452_, v_rawVal_456_);
v___y_460_ = v___x_467_;
goto v___jp_459_;
}
v___jp_459_:
{
if (v___y_460_ == 0)
{
lean_dec(v_preresolved_458_);
lean_dec(v_val_457_);
lean_dec(v_preresolved_454_);
lean_dec(v_val_453_);
return v___y_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = lean_name_eq(v_val_453_, v_val_457_);
lean_dec(v_val_457_);
lean_dec(v_val_453_);
if (v___x_461_ == 0)
{
lean_dec(v_preresolved_458_);
lean_dec(v_preresolved_454_);
return v___x_461_;
}
else
{
uint8_t v___x_462_; 
v___x_462_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_454_, v_preresolved_458_);
lean_dec(v_preresolved_458_);
lean_dec(v_preresolved_454_);
return v___x_462_;
}
}
}
}
else
{
uint8_t v___x_468_; 
lean_dec_ref_known(v_x_419_, 4);
lean_dec(v_x_420_);
v___x_468_ = 0;
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object* v_xs_469_, lean_object* v_ys_470_, lean_object* v_x_471_){
_start:
{
lean_object* v_zero_472_; uint8_t v_isZero_473_; 
v_zero_472_ = lean_unsigned_to_nat(0u);
v_isZero_473_ = lean_nat_dec_eq(v_x_471_, v_zero_472_);
if (v_isZero_473_ == 1)
{
lean_dec(v_x_471_);
return v_isZero_473_;
}
else
{
lean_object* v_one_474_; lean_object* v_n_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_one_474_ = lean_unsigned_to_nat(1u);
v_n_475_ = lean_nat_sub(v_x_471_, v_one_474_);
lean_dec(v_x_471_);
v___x_476_ = lean_array_fget_borrowed(v_xs_469_, v_n_475_);
v___x_477_ = lean_array_fget_borrowed(v_ys_470_, v_n_475_);
lean_inc(v___x_477_);
lean_inc(v___x_476_);
v___x_478_ = l_Lean_Syntax_structRangeEq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v_n_475_);
return v___x_478_;
}
else
{
v_x_471_ = v_n_475_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object* v_xs_480_, lean_object* v_ys_481_, lean_object* v_x_482_){
_start:
{
uint8_t v_res_483_; lean_object* v_r_484_; 
v_res_483_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_480_, v_ys_481_, v_x_482_);
lean_dec_ref(v_ys_481_);
lean_dec_ref(v_xs_480_);
v_r_484_ = lean_box(v_res_483_);
return v_r_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
uint8_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_Lean_Syntax_structRangeEq(v_x_485_, v_x_486_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object* v_xs_489_, lean_object* v_ys_490_, lean_object* v_hsz_491_, lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_489_, v_ys_490_, v_x_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object* v_xs_495_, lean_object* v_ys_496_, lean_object* v_hsz_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(v_xs_495_, v_ys_496_, v_hsz_497_, v_x_498_, v_x_499_);
lean_dec_ref(v_ys_496_);
lean_dec_ref(v_xs_495_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t v___x_502_, lean_object* v_x_503_){
_start:
{
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object* v___x_504_, lean_object* v_x_505_){
_start:
{
uint8_t v___x_207__boxed_506_; uint8_t v_res_507_; lean_object* v_r_508_; 
v___x_207__boxed_506_ = lean_unbox(v___x_504_);
v_res_507_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_207__boxed_506_, v_x_505_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object* v_opts_518_, lean_object* v_stx1_519_, lean_object* v_stx2_520_){
_start:
{
uint8_t v___x_521_; uint8_t v___x_522_; 
lean_inc(v_stx2_520_);
lean_inc(v_stx1_519_);
v___x_521_ = l_Lean_Syntax_structRangeEq(v_stx1_519_, v_stx2_520_);
v___x_522_ = 1;
if (v___x_521_ == 0)
{
lean_object* v_map_523_; lean_object* v___x_524_; lean_object* v___f_525_; uint8_t v___y_527_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_map_523_ = lean_ctor_get(v_opts_518_, 0);
v___x_524_ = lean_box(v___x_521_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_525_, 0, v___x_524_);
v___x_542_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_523_, v___x_542_);
if (lean_obj_tag(v___x_543_) == 0)
{
v___y_527_ = v___x_521_;
goto v___jp_526_;
}
else
{
lean_object* v_val_544_; 
v_val_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_544_);
lean_dec_ref_known(v___x_543_, 1);
if (lean_obj_tag(v_val_544_) == 1)
{
uint8_t v_v_545_; 
v_v_545_ = lean_ctor_get_uint8(v_val_544_, 0);
lean_dec_ref_known(v_val_544_, 0);
v___y_527_ = v_v_545_;
goto v___jp_526_;
}
else
{
lean_dec(v_val_544_);
v___y_527_ = v___x_521_;
goto v___jp_526_;
}
}
v___jp_526_:
{
if (v___y_527_ == 0)
{
lean_dec_ref(v___f_525_);
lean_dec(v_stx2_520_);
lean_dec(v_stx1_519_);
return v___x_521_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_528_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_529_ = lean_box(0);
v___x_530_ = l_Lean_Syntax_formatStx(v_stx1_519_, v___x_529_, v___x_522_);
v___x_531_ = l_Std_Format_defWidth;
v___x_532_ = lean_unsigned_to_nat(0u);
v___x_533_ = l_Std_Format_pretty(v___x_530_, v___x_531_, v___x_532_, v___x_532_);
v___x_534_ = lean_string_append(v___x_528_, v___x_533_);
lean_dec_ref(v___x_533_);
v___x_535_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_536_ = lean_string_append(v___x_534_, v___x_535_);
v___x_537_ = l_Lean_Syntax_formatStx(v_stx2_520_, v___x_529_, v___x_522_);
v___x_538_ = l_Std_Format_pretty(v___x_537_, v___x_531_, v___x_532_, v___x_532_);
v___x_539_ = lean_string_append(v___x_536_, v___x_538_);
lean_dec_ref(v___x_538_);
v___x_540_ = lean_dbg_trace(v___x_539_, v___f_525_);
v___x_541_ = lean_unbox(v___x_540_);
lean_dec(v___x_540_);
return v___x_541_;
}
}
}
else
{
lean_dec(v_stx2_520_);
lean_dec(v_stx1_519_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object* v_opts_546_, lean_object* v_stx1_547_, lean_object* v_stx2_548_){
_start:
{
uint8_t v_res_549_; lean_object* v_r_550_; 
v_res_549_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_546_, v_stx1_547_, v_stx2_548_);
lean_dec_ref(v_opts_546_);
v_r_550_ = lean_box(v_res_549_);
return v_r_550_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
switch(lean_obj_tag(v_x_551_))
{
case 0:
{
if (lean_obj_tag(v_x_552_) == 0)
{
uint8_t v___x_553_; 
v___x_553_ = 1;
return v___x_553_;
}
else
{
uint8_t v___x_554_; 
lean_dec(v_x_552_);
v___x_554_ = 0;
return v___x_554_;
}
}
case 1:
{
if (lean_obj_tag(v_x_552_) == 1)
{
lean_object* v_info_555_; lean_object* v_kind_556_; lean_object* v_args_557_; lean_object* v_info_558_; lean_object* v_kind_559_; lean_object* v_args_560_; uint8_t v___y_562_; uint8_t v___x_567_; 
v_info_555_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_info_555_);
v_kind_556_ = lean_ctor_get(v_x_551_, 1);
lean_inc(v_kind_556_);
v_args_557_ = lean_ctor_get(v_x_551_, 2);
lean_inc_ref(v_args_557_);
lean_dec_ref_known(v_x_551_, 3);
v_info_558_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_info_558_);
v_kind_559_ = lean_ctor_get(v_x_552_, 1);
lean_inc(v_kind_559_);
v_args_560_ = lean_ctor_get(v_x_552_, 2);
lean_inc_ref(v_args_560_);
lean_dec_ref_known(v_x_552_, 3);
v___x_567_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_555_, v_info_558_);
if (v___x_567_ == 0)
{
lean_dec(v_kind_559_);
lean_dec(v_kind_556_);
v___y_562_ = v___x_567_;
goto v___jp_561_;
}
else
{
uint8_t v___x_568_; 
v___x_568_ = lean_name_eq(v_kind_556_, v_kind_559_);
lean_dec(v_kind_559_);
lean_dec(v_kind_556_);
v___y_562_ = v___x_568_;
goto v___jp_561_;
}
v___jp_561_:
{
if (v___y_562_ == 0)
{
lean_dec_ref(v_args_560_);
lean_dec_ref(v_args_557_);
return v___y_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = lean_array_get_size(v_args_557_);
v___x_564_ = lean_array_get_size(v_args_560_);
v___x_565_ = lean_nat_dec_eq(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_dec_ref(v_args_560_);
lean_dec_ref(v_args_557_);
return v___x_565_;
}
else
{
uint8_t v___x_566_; 
v___x_566_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_args_557_, v_args_560_, v___x_563_);
lean_dec_ref(v_args_560_);
lean_dec_ref(v_args_557_);
return v___x_566_;
}
}
}
}
else
{
uint8_t v___x_569_; 
lean_dec_ref_known(v_x_551_, 3);
lean_dec(v_x_552_);
v___x_569_ = 0;
return v___x_569_;
}
}
case 2:
{
if (lean_obj_tag(v_x_552_) == 2)
{
lean_object* v_info_570_; lean_object* v_val_571_; lean_object* v_info_572_; lean_object* v_val_573_; uint8_t v___x_574_; 
v_info_570_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_info_570_);
v_val_571_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_val_571_);
lean_dec_ref_known(v_x_551_, 2);
v_info_572_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_info_572_);
v_val_573_ = lean_ctor_get(v_x_552_, 1);
lean_inc_ref(v_val_573_);
lean_dec_ref_known(v_x_552_, 2);
v___x_574_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_570_, v_info_572_);
if (v___x_574_ == 0)
{
lean_dec_ref(v_val_573_);
lean_dec_ref(v_val_571_);
return v___x_574_;
}
else
{
uint8_t v___x_575_; 
v___x_575_ = lean_string_dec_eq(v_val_571_, v_val_573_);
lean_dec_ref(v_val_573_);
lean_dec_ref(v_val_571_);
return v___x_575_;
}
}
else
{
uint8_t v___x_576_; 
lean_dec_ref_known(v_x_551_, 2);
lean_dec(v_x_552_);
v___x_576_ = 0;
return v___x_576_;
}
}
default: 
{
if (lean_obj_tag(v_x_552_) == 3)
{
lean_object* v_info_577_; lean_object* v_rawVal_578_; lean_object* v_val_579_; lean_object* v_preresolved_580_; lean_object* v_info_581_; lean_object* v_rawVal_582_; lean_object* v_val_583_; lean_object* v_preresolved_584_; uint8_t v___y_586_; uint8_t v___x_589_; 
v_info_577_ = lean_ctor_get(v_x_551_, 0);
lean_inc(v_info_577_);
v_rawVal_578_ = lean_ctor_get(v_x_551_, 1);
lean_inc_ref(v_rawVal_578_);
v_val_579_ = lean_ctor_get(v_x_551_, 2);
lean_inc(v_val_579_);
v_preresolved_580_ = lean_ctor_get(v_x_551_, 3);
lean_inc(v_preresolved_580_);
lean_dec_ref_known(v_x_551_, 4);
v_info_581_ = lean_ctor_get(v_x_552_, 0);
lean_inc(v_info_581_);
v_rawVal_582_ = lean_ctor_get(v_x_552_, 1);
lean_inc_ref(v_rawVal_582_);
v_val_583_ = lean_ctor_get(v_x_552_, 2);
lean_inc(v_val_583_);
v_preresolved_584_ = lean_ctor_get(v_x_552_, 3);
lean_inc(v_preresolved_584_);
lean_dec_ref_known(v_x_552_, 4);
v___x_589_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_577_, v_info_581_);
if (v___x_589_ == 0)
{
lean_dec_ref(v_rawVal_582_);
lean_dec_ref(v_rawVal_578_);
v___y_586_ = v___x_589_;
goto v___jp_585_;
}
else
{
uint8_t v___x_590_; 
v___x_590_ = l_Substring_Raw_beq(v_rawVal_578_, v_rawVal_582_);
v___y_586_ = v___x_590_;
goto v___jp_585_;
}
v___jp_585_:
{
if (v___y_586_ == 0)
{
lean_dec(v_preresolved_584_);
lean_dec(v_val_583_);
lean_dec(v_preresolved_580_);
lean_dec(v_val_579_);
return v___y_586_;
}
else
{
uint8_t v___x_587_; 
v___x_587_ = lean_name_eq(v_val_579_, v_val_583_);
lean_dec(v_val_583_);
lean_dec(v_val_579_);
if (v___x_587_ == 0)
{
lean_dec(v_preresolved_584_);
lean_dec(v_preresolved_580_);
return v___x_587_;
}
else
{
uint8_t v___x_588_; 
v___x_588_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_580_, v_preresolved_584_);
lean_dec(v_preresolved_584_);
lean_dec(v_preresolved_580_);
return v___x_588_;
}
}
}
}
else
{
uint8_t v___x_591_; 
lean_dec_ref_known(v_x_551_, 4);
lean_dec(v_x_552_);
v___x_591_ = 0;
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object* v_xs_592_, lean_object* v_ys_593_, lean_object* v_x_594_){
_start:
{
lean_object* v_zero_595_; uint8_t v_isZero_596_; 
v_zero_595_ = lean_unsigned_to_nat(0u);
v_isZero_596_ = lean_nat_dec_eq(v_x_594_, v_zero_595_);
if (v_isZero_596_ == 1)
{
lean_dec(v_x_594_);
return v_isZero_596_;
}
else
{
lean_object* v_one_597_; lean_object* v_n_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_one_597_ = lean_unsigned_to_nat(1u);
v_n_598_ = lean_nat_sub(v_x_594_, v_one_597_);
lean_dec(v_x_594_);
v___x_599_ = lean_array_fget_borrowed(v_xs_592_, v_n_598_);
v___x_600_ = lean_array_fget_borrowed(v_ys_593_, v_n_598_);
lean_inc(v___x_600_);
lean_inc(v___x_599_);
v___x_601_ = l_Lean_Syntax_eqWithInfo(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_dec(v_n_598_);
return v___x_601_;
}
else
{
v_x_594_ = v_n_598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object* v_xs_603_, lean_object* v_ys_604_, lean_object* v_x_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_603_, v_ys_604_, v_x_605_);
lean_dec_ref(v_ys_604_);
lean_dec_ref(v_xs_603_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Lean_Syntax_eqWithInfo(v_x_608_, v_x_609_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object* v_xs_612_, lean_object* v_ys_613_, lean_object* v_hsz_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_612_, v_ys_613_, v_x_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object* v_xs_618_, lean_object* v_ys_619_, lean_object* v_hsz_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
uint8_t v_res_623_; lean_object* v_r_624_; 
v_res_623_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_618_, v_ys_619_, v_hsz_620_, v_x_621_, v_x_622_);
lean_dec_ref(v_ys_619_);
lean_dec_ref(v_xs_618_);
v_r_624_ = lean_box(v_res_623_);
return v_r_624_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object* v_opts_625_, lean_object* v_stx1_626_, lean_object* v_stx2_627_){
_start:
{
uint8_t v___x_628_; uint8_t v___x_629_; 
lean_inc(v_stx2_627_);
lean_inc(v_stx1_626_);
v___x_628_ = l_Lean_Syntax_eqWithInfo(v_stx1_626_, v_stx2_627_);
v___x_629_ = 1;
if (v___x_628_ == 0)
{
lean_object* v_map_630_; lean_object* v___x_631_; lean_object* v___f_632_; uint8_t v___y_634_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_map_630_ = lean_ctor_get(v_opts_625_, 0);
v___x_631_ = lean_box(v___x_628_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_632_, 0, v___x_631_);
v___x_649_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_650_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_630_, v___x_649_);
if (lean_obj_tag(v___x_650_) == 0)
{
v___y_634_ = v___x_628_;
goto v___jp_633_;
}
else
{
lean_object* v_val_651_; 
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v___x_650_, 1);
if (lean_obj_tag(v_val_651_) == 1)
{
uint8_t v_v_652_; 
v_v_652_ = lean_ctor_get_uint8(v_val_651_, 0);
lean_dec_ref_known(v_val_651_, 0);
v___y_634_ = v_v_652_;
goto v___jp_633_;
}
else
{
lean_dec(v_val_651_);
v___y_634_ = v___x_628_;
goto v___jp_633_;
}
}
v___jp_633_:
{
if (v___y_634_ == 0)
{
lean_dec_ref(v___f_632_);
lean_dec(v_stx2_627_);
lean_dec(v_stx1_626_);
return v___x_628_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_635_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_636_ = lean_box(0);
v___x_637_ = l_Lean_Syntax_formatStx(v_stx1_626_, v___x_636_, v___x_629_);
v___x_638_ = l_Std_Format_defWidth;
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = l_Std_Format_pretty(v___x_637_, v___x_638_, v___x_639_, v___x_639_);
v___x_641_ = lean_string_append(v___x_635_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
v___x_644_ = l_Lean_Syntax_formatStx(v_stx2_627_, v___x_636_, v___x_629_);
v___x_645_ = l_Std_Format_pretty(v___x_644_, v___x_638_, v___x_639_, v___x_639_);
v___x_646_ = lean_string_append(v___x_643_, v___x_645_);
lean_dec_ref(v___x_645_);
v___x_647_ = lean_dbg_trace(v___x_646_, v___f_632_);
v___x_648_ = lean_unbox(v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
}
else
{
lean_dec(v_stx2_627_);
lean_dec(v_stx1_626_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object* v_opts_653_, lean_object* v_stx1_654_, lean_object* v_stx2_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_653_, v_stx1_654_, v_stx2_655_);
lean_dec_ref(v_opts_653_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_659_) == 2)
{
lean_object* v_val_660_; 
v_val_660_ = lean_ctor_get(v_x_659_, 1);
lean_inc_ref(v_val_660_);
return v_val_660_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Syntax_getAtomVal(v_x_662_);
lean_dec(v_x_662_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
if (lean_obj_tag(v_x_664_) == 2)
{
lean_object* v_info_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_info_666_ = lean_ctor_get(v_x_664_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v_x_664_, 1);
lean_dec(v_unused_674_);
v___x_668_ = v_x_664_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_info_666_);
lean_dec(v_x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v_x_665_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_info_666_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_x_665_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_dec_ref(v_x_665_);
return v_x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object* v_stx_675_, lean_object* v_hyes_676_, lean_object* v_hno_677_){
_start:
{
if (lean_obj_tag(v_stx_675_) == 1)
{
lean_object* v___x_678_; 
lean_dec(v_hno_677_);
v___x_678_ = lean_apply_1(v_hyes_676_, v_stx_675_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_hyes_676_);
lean_dec(v_stx_675_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_apply_1(v_hno_677_, v___x_679_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object* v_00_u03b2_681_, lean_object* v_stx_682_, lean_object* v_hyes_683_, lean_object* v_hno_684_){
_start:
{
if (lean_obj_tag(v_stx_682_) == 1)
{
lean_object* v___x_685_; 
lean_dec(v_hno_684_);
v___x_685_ = lean_apply_1(v_hyes_683_, v_stx_682_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec(v_hyes_683_);
lean_dec(v_stx_682_);
v___x_686_ = lean_box(0);
v___x_687_ = lean_apply_1(v_hno_684_, v___x_686_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object* v_stx_688_, lean_object* v_kind_689_, lean_object* v_hyes_690_, lean_object* v_hno_691_){
_start:
{
if (lean_obj_tag(v_stx_688_) == 1)
{
lean_object* v_kind_692_; uint8_t v___x_693_; 
v_kind_692_ = lean_ctor_get(v_stx_688_, 1);
v___x_693_ = lean_name_eq(v_kind_692_, v_kind_689_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_dec_ref_known(v_stx_688_, 3);
lean_dec(v_hyes_690_);
v___x_694_ = lean_box(0);
v___x_695_ = lean_apply_1(v_hno_691_, v___x_694_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; 
lean_dec(v_hno_691_);
v___x_696_ = lean_apply_1(v_hyes_690_, v_stx_688_);
return v___x_696_;
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec(v_hyes_690_);
lean_dec(v_stx_688_);
v___x_697_ = lean_box(0);
v___x_698_ = lean_apply_1(v_hno_691_, v___x_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object* v_stx_699_, lean_object* v_kind_700_, lean_object* v_hyes_701_, lean_object* v_hno_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Lean_Syntax_ifNodeKind___redArg(v_stx_699_, v_kind_700_, v_hyes_701_, v_hno_702_);
lean_dec(v_kind_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object* v_00_u03b2_704_, lean_object* v_stx_705_, lean_object* v_kind_706_, lean_object* v_hyes_707_, lean_object* v_hno_708_){
_start:
{
if (lean_obj_tag(v_stx_705_) == 1)
{
lean_object* v_kind_709_; uint8_t v___x_710_; 
v_kind_709_ = lean_ctor_get(v_stx_705_, 1);
v___x_710_ = lean_name_eq(v_kind_709_, v_kind_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec_ref_known(v_stx_705_, 3);
lean_dec(v_hyes_707_);
v___x_711_ = lean_box(0);
v___x_712_ = lean_apply_1(v_hno_708_, v___x_711_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; 
lean_dec(v_hno_708_);
v___x_713_ = lean_apply_1(v_hyes_707_, v_stx_705_);
return v___x_713_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v_hyes_707_);
lean_dec(v_stx_705_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_apply_1(v_hno_708_, v___x_714_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object* v_00_u03b2_716_, lean_object* v_stx_717_, lean_object* v_kind_718_, lean_object* v_hyes_719_, lean_object* v_hno_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Syntax_ifNodeKind(v_00_u03b2_716_, v_stx_717_, v_kind_718_, v_hyes_719_, v_hno_720_);
lean_dec(v_kind_718_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_731_) == 1)
{
lean_inc_ref(v_x_731_);
return v_x_731_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Syntax_asNode(v_x_733_);
lean_dec(v_x_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object* v_stx_735_, lean_object* v_i_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Lean_Syntax_getArg(v_stx_735_, v_i_736_);
v___x_738_ = l_Lean_Syntax_getId(v___x_737_);
lean_dec(v___x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* v_stx_739_, lean_object* v_i_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Syntax_getIdAt(v_stx_739_, v_i_740_);
lean_dec(v_i_740_);
lean_dec(v_stx_739_);
return v_res_741_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object* v_id_742_, lean_object* v_x_743_){
_start:
{
switch(lean_obj_tag(v_x_743_))
{
case 3:
{
lean_object* v_val_744_; uint8_t v___x_745_; 
v_val_744_ = lean_ctor_get(v_x_743_, 2);
v___x_745_ = lean_name_eq(v_id_742_, v_val_744_);
return v___x_745_;
}
case 1:
{
lean_object* v_args_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_args_746_ = lean_ctor_get(v_x_743_, 2);
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_array_get_size(v_args_746_);
v___x_749_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
return v___x_749_;
}
else
{
if (v___x_749_ == 0)
{
return v___x_749_;
}
else
{
size_t v___x_750_; size_t v___x_751_; uint8_t v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_748_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_742_, v_args_746_, v___x_750_, v___x_751_);
return v___x_752_;
}
}
}
default: 
{
uint8_t v___x_753_; 
v___x_753_ = 0;
return v___x_753_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object* v_id_754_, lean_object* v_as_755_, size_t v_i_756_, size_t v_stop_757_){
_start:
{
uint8_t v___x_758_; 
v___x_758_ = lean_usize_dec_eq(v_i_756_, v_stop_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_uget_borrowed(v_as_755_, v_i_756_);
v___x_760_ = l_Lean_Syntax_hasIdent(v_id_754_, v___x_759_);
if (v___x_760_ == 0)
{
size_t v___x_761_; size_t v___x_762_; 
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_756_, v___x_761_);
v_i_756_ = v___x_762_;
goto _start;
}
else
{
return v___x_760_;
}
}
else
{
uint8_t v___x_764_; 
v___x_764_ = 0;
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object* v_id_765_, lean_object* v_as_766_, lean_object* v_i_767_, lean_object* v_stop_768_){
_start:
{
size_t v_i_boxed_769_; size_t v_stop_boxed_770_; uint8_t v_res_771_; lean_object* v_r_772_; 
v_i_boxed_769_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_stop_boxed_770_ = lean_unbox_usize(v_stop_768_);
lean_dec(v_stop_768_);
v_res_771_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_765_, v_as_766_, v_i_boxed_769_, v_stop_boxed_770_);
lean_dec_ref(v_as_766_);
lean_dec(v_id_765_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object* v_id_773_, lean_object* v_x_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Lean_Syntax_hasIdent(v_id_773_, v_x_774_);
lean_dec(v_x_774_);
lean_dec(v_id_773_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object* v_stx_777_, lean_object* v_fn_778_){
_start:
{
if (lean_obj_tag(v_stx_777_) == 1)
{
lean_object* v_info_779_; lean_object* v_kind_780_; lean_object* v_args_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_info_779_ = lean_ctor_get(v_stx_777_, 0);
v_kind_780_ = lean_ctor_get(v_stx_777_, 1);
v_args_781_ = lean_ctor_get(v_stx_777_, 2);
v_isSharedCheck_789_ = !lean_is_exclusive(v_stx_777_);
if (v_isSharedCheck_789_ == 0)
{
v___x_783_ = v_stx_777_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_args_781_);
lean_inc(v_kind_780_);
lean_inc(v_info_779_);
lean_dec(v_stx_777_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = lean_apply_1(v_fn_778_, v_args_781_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 2, v___x_785_);
v___x_787_ = v___x_783_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_info_779_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_kind_780_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
else
{
lean_dec_ref(v_fn_778_);
return v_stx_777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object* v_stx_790_, lean_object* v_i_791_, lean_object* v_fn_792_){
_start:
{
if (lean_obj_tag(v_stx_790_) == 1)
{
lean_object* v_info_793_; lean_object* v_kind_794_; lean_object* v_args_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_info_793_ = lean_ctor_get(v_stx_790_, 0);
v_kind_794_ = lean_ctor_get(v_stx_790_, 1);
v_args_795_ = lean_ctor_get(v_stx_790_, 2);
v___x_796_ = lean_array_get_size(v_args_795_);
v___x_797_ = lean_nat_dec_lt(v_i_791_, v___x_796_);
if (v___x_797_ == 0)
{
lean_dec_ref(v_fn_792_);
return v_stx_790_;
}
else
{
lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_809_; 
lean_inc_ref(v_args_795_);
lean_inc(v_kind_794_);
lean_inc(v_info_793_);
v_isSharedCheck_809_ = !lean_is_exclusive(v_stx_790_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_810_ = lean_ctor_get(v_stx_790_, 2);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_stx_790_, 1);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_stx_790_, 0);
lean_dec(v_unused_812_);
v___x_799_ = v_stx_790_;
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
else
{
lean_dec(v_stx_790_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_809_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_v_801_; lean_object* v___x_802_; lean_object* v_xs_x27_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v_v_801_ = lean_array_fget(v_args_795_, v_i_791_);
v___x_802_ = lean_box(0);
v_xs_x27_803_ = lean_array_fset(v_args_795_, v_i_791_, v___x_802_);
v___x_804_ = lean_apply_1(v_fn_792_, v_v_801_);
v___x_805_ = lean_array_fset(v_xs_x27_803_, v_i_791_, v___x_804_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 2, v___x_805_);
v___x_807_ = v___x_799_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_info_793_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_kind_794_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_dec_ref(v_fn_792_);
return v_stx_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* v_stx_813_, lean_object* v_i_814_, lean_object* v_fn_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Syntax_modifyArg(v_stx_813_, v_i_814_, v_fn_815_);
lean_dec(v_i_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object* v_info_817_, lean_object* v_kind_818_, lean_object* v_toPure_819_, lean_object* v_____do__lift_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_821_, 0, v_info_817_);
lean_ctor_set(v___x_821_, 1, v_kind_818_);
lean_ctor_set(v___x_821_, 2, v_____do__lift_820_);
v___x_822_ = lean_apply_2(v_toPure_819_, lean_box(0), v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object* v_toPure_823_, lean_object* v_x_824_, lean_object* v_o_825_){
_start:
{
if (lean_obj_tag(v_o_825_) == 0)
{
lean_object* v___x_826_; 
v___x_826_ = lean_apply_2(v_toPure_823_, lean_box(0), v_x_824_);
return v___x_826_;
}
else
{
lean_object* v_val_827_; lean_object* v___x_828_; 
lean_dec(v_x_824_);
v_val_827_ = lean_ctor_get(v_o_825_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v_o_825_, 1);
v___x_828_ = lean_apply_2(v_toPure_823_, lean_box(0), v_val_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object* v_inst_829_, lean_object* v_fn_830_, lean_object* v_x_831_){
_start:
{
if (lean_obj_tag(v_x_831_) == 1)
{
lean_object* v_toApplicative_832_; lean_object* v_toBind_833_; lean_object* v_toPure_834_; lean_object* v_info_835_; lean_object* v_kind_836_; lean_object* v_args_837_; lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_toApplicative_832_ = lean_ctor_get(v_inst_829_, 0);
v_toBind_833_ = lean_ctor_get(v_inst_829_, 1);
lean_inc_n(v_toBind_833_, 2);
v_toPure_834_ = lean_ctor_get(v_toApplicative_832_, 1);
lean_inc_n(v_toPure_834_, 2);
v_info_835_ = lean_ctor_get(v_x_831_, 0);
v_kind_836_ = lean_ctor_get(v_x_831_, 1);
v_args_837_ = lean_ctor_get(v_x_831_, 2);
lean_inc(v_kind_836_);
lean_inc(v_info_835_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_838_, 0, v_info_835_);
lean_closure_set(v___f_838_, 1, v_kind_836_);
lean_closure_set(v___f_838_, 2, v_toPure_834_);
lean_inc_ref(v_args_837_);
lean_inc(v_fn_830_);
v___f_839_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_839_, 0, v_inst_829_);
lean_closure_set(v___f_839_, 1, v_fn_830_);
lean_closure_set(v___f_839_, 2, v_args_837_);
lean_closure_set(v___f_839_, 3, v_toBind_833_);
lean_closure_set(v___f_839_, 4, v___f_838_);
lean_closure_set(v___f_839_, 5, v_toPure_834_);
v___x_840_ = lean_apply_1(v_fn_830_, v_x_831_);
v___x_841_ = lean_apply_4(v_toBind_833_, lean_box(0), lean_box(0), v___x_840_, v___f_839_);
return v___x_841_;
}
else
{
lean_object* v_toApplicative_842_; lean_object* v_toBind_843_; lean_object* v_toPure_844_; lean_object* v___f_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_toApplicative_842_ = lean_ctor_get(v_inst_829_, 0);
lean_inc_ref(v_toApplicative_842_);
v_toBind_843_ = lean_ctor_get(v_inst_829_, 1);
lean_inc(v_toBind_843_);
lean_dec_ref(v_inst_829_);
v_toPure_844_ = lean_ctor_get(v_toApplicative_842_, 1);
lean_inc(v_toPure_844_);
lean_dec_ref(v_toApplicative_842_);
lean_inc(v_x_831_);
v___f_845_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_845_, 0, v_toPure_844_);
lean_closure_set(v___f_845_, 1, v_x_831_);
v___x_846_ = lean_apply_1(v_fn_830_, v_x_831_);
v___x_847_ = lean_apply_4(v_toBind_843_, lean_box(0), lean_box(0), v___x_846_, v___f_845_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object* v_inst_848_, lean_object* v_fn_849_, lean_object* v_args_850_, lean_object* v_toBind_851_, lean_object* v___f_852_, lean_object* v_toPure_853_, lean_object* v_____do__lift_854_){
_start:
{
if (lean_obj_tag(v_____do__lift_854_) == 0)
{
lean_object* v___x_855_; size_t v_sz_856_; size_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_toPure_853_);
lean_inc_ref(v_inst_848_);
v___x_855_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg), 3, 2);
lean_closure_set(v___x_855_, 0, v_inst_848_);
lean_closure_set(v___x_855_, 1, v_fn_849_);
v_sz_856_ = lean_array_size(v_args_850_);
v___x_857_ = ((size_t)0ULL);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_848_, v___x_855_, v_sz_856_, v___x_857_, v_args_850_);
v___x_859_ = lean_apply_4(v_toBind_851_, lean_box(0), lean_box(0), v___x_858_, v___f_852_);
return v___x_859_;
}
else
{
lean_object* v_val_860_; lean_object* v___x_861_; 
lean_dec(v___f_852_);
lean_dec(v_toBind_851_);
lean_dec_ref(v_args_850_);
lean_dec(v_fn_849_);
lean_dec_ref(v_inst_848_);
v_val_860_ = lean_ctor_get(v_____do__lift_854_, 0);
lean_inc(v_val_860_);
lean_dec_ref_known(v_____do__lift_854_, 1);
v___x_861_ = lean_apply_2(v_toPure_853_, lean_box(0), v_val_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object* v_m_862_, lean_object* v_inst_863_, lean_object* v_fn_864_, lean_object* v_x_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Syntax_replaceM___redArg(v_inst_863_, v_fn_864_, v_x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object* v_info_867_, lean_object* v_kind_868_, lean_object* v_fn_869_, lean_object* v_args_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_871_, 0, v_info_867_);
lean_ctor_set(v___x_871_, 1, v_kind_868_);
lean_ctor_set(v___x_871_, 2, v_args_870_);
v___x_872_ = lean_apply_1(v_fn_869_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object* v_inst_873_, lean_object* v_fn_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 1)
{
lean_object* v_toBind_876_; lean_object* v_info_877_; lean_object* v_kind_878_; lean_object* v_args_879_; lean_object* v___f_880_; lean_object* v___x_881_; size_t v_sz_882_; size_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_toBind_876_ = lean_ctor_get(v_inst_873_, 1);
lean_inc(v_toBind_876_);
v_info_877_ = lean_ctor_get(v_x_875_, 0);
lean_inc(v_info_877_);
v_kind_878_ = lean_ctor_get(v_x_875_, 1);
lean_inc(v_kind_878_);
v_args_879_ = lean_ctor_get(v_x_875_, 2);
lean_inc_ref(v_args_879_);
lean_dec_ref_known(v_x_875_, 3);
lean_inc(v_fn_874_);
v___f_880_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_880_, 0, v_info_877_);
lean_closure_set(v___f_880_, 1, v_kind_878_);
lean_closure_set(v___f_880_, 2, v_fn_874_);
lean_inc_ref(v_inst_873_);
v___x_881_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg), 3, 2);
lean_closure_set(v___x_881_, 0, v_inst_873_);
lean_closure_set(v___x_881_, 1, v_fn_874_);
v_sz_882_ = lean_array_size(v_args_879_);
v___x_883_ = ((size_t)0ULL);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_873_, v___x_881_, v_sz_882_, v___x_883_, v_args_879_);
v___x_885_ = lean_apply_4(v_toBind_876_, lean_box(0), lean_box(0), v___x_884_, v___f_880_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
lean_dec_ref(v_inst_873_);
v___x_886_ = lean_apply_1(v_fn_874_, v_x_875_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* v_m_887_, lean_object* v_inst_888_, lean_object* v_fn_889_, lean_object* v_x_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_888_, v_fn_889_, v_x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object* v_fn_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_apply_1(v_fn_892_, v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* v_fn_914_, lean_object* v_stx_915_){
_start:
{
lean_object* v___f_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUp___lam__0), 2, 1);
lean_closure_set(v___f_916_, 0, v_fn_914_);
v___x_917_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUp___closed__9));
v___x_918_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_917_, v___f_916_, v_stx_915_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_object* v_leading_922_; lean_object* v_trailing_923_; lean_object* v_pos_924_; lean_object* v_endPos_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_952_; 
v_leading_922_ = lean_ctor_get(v_x_919_, 0);
v_trailing_923_ = lean_ctor_get(v_x_919_, 2);
v_pos_924_ = lean_ctor_get(v_x_919_, 1);
v_endPos_925_ = lean_ctor_get(v_x_919_, 3);
v_isSharedCheck_952_ = !lean_is_exclusive(v_x_919_);
if (v_isSharedCheck_952_ == 0)
{
v___x_927_ = v_x_919_;
v_isShared_928_ = v_isSharedCheck_952_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_endPos_925_);
lean_inc(v_trailing_923_);
lean_inc(v_pos_924_);
lean_inc(v_leading_922_);
lean_dec(v_x_919_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_952_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_str_929_; lean_object* v_stopPos_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_950_; 
v_str_929_ = lean_ctor_get(v_leading_922_, 0);
v_stopPos_930_ = lean_ctor_get(v_leading_922_, 2);
v_isSharedCheck_950_ = !lean_is_exclusive(v_leading_922_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_leading_922_, 1);
lean_dec(v_unused_951_);
v___x_932_ = v_leading_922_;
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_stopPos_930_);
lean_inc(v_str_929_);
lean_dec(v_leading_922_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v_str_934_; lean_object* v_startPos_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_948_; 
v_str_934_ = lean_ctor_get(v_trailing_923_, 0);
v_startPos_935_ = lean_ctor_get(v_trailing_923_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_trailing_923_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_trailing_923_, 2);
lean_dec(v_unused_949_);
v___x_937_ = v_trailing_923_;
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_startPos_935_);
lean_inc(v_str_934_);
lean_dec(v_trailing_923_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_948_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 2, v_stopPos_930_);
lean_ctor_set(v___x_937_, 1, v_x_920_);
lean_ctor_set(v___x_937_, 0, v_str_929_);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_str_929_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_x_920_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_stopPos_930_);
v___x_940_ = v_reuseFailAlloc_947_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 2, v_x_921_);
lean_ctor_set(v___x_932_, 1, v_startPos_935_);
lean_ctor_set(v___x_932_, 0, v_str_934_);
v___x_942_ = v___x_932_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_str_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_startPos_935_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_x_921_);
v___x_942_ = v_reuseFailAlloc_946_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_944_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 2, v___x_942_);
lean_ctor_set(v___x_927_, 0, v___x_940_);
v___x_944_ = v___x_927_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_pos_924_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_endPos_925_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_921_);
lean_dec(v_x_920_);
return v_x_919_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_953_, lean_object* v___x_954_, lean_object* v___x_955_, lean_object* v_a_956_, lean_object* v_b_957_){
_start:
{
lean_object* v_startInclusive_958_; lean_object* v_endExclusive_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v_startInclusive_958_ = lean_ctor_get(v___x_953_, 1);
v_endExclusive_959_ = lean_ctor_get(v___x_953_, 2);
v___x_960_ = lean_nat_sub(v_endExclusive_959_, v_startInclusive_958_);
v___x_961_ = lean_nat_dec_eq(v_a_956_, v___x_960_);
lean_dec(v___x_960_);
if (v___x_961_ == 0)
{
uint32_t v___x_962_; lean_object* v___x_963_; uint32_t v___x_964_; uint8_t v___x_965_; 
v___x_962_ = 10;
v___x_963_ = lean_nat_add(v___x_954_, v_a_956_);
v___x_964_ = lean_string_utf8_get_fast(v___x_955_, v___x_963_);
v___x_965_ = lean_uint32_dec_eq(v___x_964_, v___x_962_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_a_956_);
v___x_966_ = lean_box(0);
v___x_967_ = lean_string_utf8_next_fast(v___x_955_, v___x_963_);
lean_dec(v___x_963_);
v___x_968_ = lean_nat_sub(v___x_967_, v___x_954_);
v_a_956_ = v___x_968_;
v_b_957_ = v___x_966_;
goto _start;
}
else
{
lean_object* v___x_970_; 
lean_dec(v___x_963_);
v___x_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_970_, 0, v_a_956_);
return v___x_970_;
}
}
else
{
lean_dec(v_a_956_);
lean_inc(v_b_957_);
return v_b_957_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_971_, lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v_a_974_, lean_object* v_b_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_971_, v___x_972_, v___x_973_, v_a_974_, v_b_975_);
lean_dec(v_b_975_);
lean_dec_ref(v___x_973_);
lean_dec(v___x_972_);
lean_dec_ref(v___x_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_977_){
_start:
{
lean_object* v_str_978_; lean_object* v_startPos_979_; lean_object* v_stopPos_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1000_; 
v_str_978_ = lean_ctor_get(v_trail_977_, 0);
v_startPos_979_ = lean_ctor_get(v_trail_977_, 1);
v_stopPos_980_ = lean_ctor_get(v_trail_977_, 2);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_trail_977_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_982_ = v_trail_977_;
v_isShared_983_ = v_isSharedCheck_1000_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_stopPos_980_);
lean_inc(v_startPos_979_);
lean_inc(v_str_978_);
lean_dec(v_trail_977_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1000_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
uint8_t v___x_987_; 
v___x_987_ = lean_string_is_valid_pos(v_str_978_, v_startPos_979_);
if (v___x_987_ == 0)
{
lean_del_object(v___x_982_);
lean_dec_ref(v_str_978_);
goto v___jp_984_;
}
else
{
uint8_t v___x_988_; 
v___x_988_ = lean_string_is_valid_pos(v_str_978_, v_stopPos_980_);
if (v___x_988_ == 0)
{
lean_del_object(v___x_982_);
lean_dec_ref(v_str_978_);
goto v___jp_984_;
}
else
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_le(v_startPos_979_, v_stopPos_980_);
if (v___x_989_ == 0)
{
lean_del_object(v___x_982_);
lean_dec_ref(v_str_978_);
goto v___jp_984_;
}
else
{
lean_object* v___x_991_; 
lean_inc(v_stopPos_980_);
lean_inc(v_startPos_979_);
lean_inc_ref(v_str_978_);
if (v_isShared_983_ == 0)
{
v___x_991_ = v___x_982_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_str_978_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_startPos_979_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_stopPos_980_);
v___x_991_ = v_reuseFailAlloc_999_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v_searcher_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_searcher_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_box(0);
v___x_994_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_991_, v_startPos_979_, v_str_978_, v_searcher_992_, v___x_993_);
lean_dec_ref(v_str_978_);
lean_dec_ref(v___x_991_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_nat_sub(v_stopPos_980_, v_startPos_979_);
lean_dec(v_stopPos_980_);
v___x_996_ = lean_nat_add(v_startPos_979_, v___x_995_);
lean_dec(v___x_995_);
lean_dec(v_startPos_979_);
return v___x_996_;
}
else
{
lean_object* v_val_997_; lean_object* v___x_998_; 
lean_dec(v_stopPos_980_);
v_val_997_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_997_);
lean_dec_ref_known(v___x_994_, 1);
v___x_998_ = lean_nat_add(v_startPos_979_, v_val_997_);
lean_dec(v_val_997_);
lean_dec(v_startPos_979_);
return v___x_998_;
}
}
}
}
}
v___jp_984_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_nat_sub(v_stopPos_980_, v_startPos_979_);
lean_dec(v_stopPos_980_);
v___x_986_ = lean_nat_add(v_startPos_979_, v___x_985_);
lean_dec(v___x_985_);
lean_dec(v_startPos_979_);
return v___x_986_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1001_, lean_object* v___x_1002_, lean_object* v___x_1003_, lean_object* v_inst_1004_, lean_object* v_R_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_, lean_object* v_c_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1001_, v___x_1002_, v___x_1003_, v_a_1006_, v_b_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v_inst_1013_, lean_object* v_R_1014_, lean_object* v_a_1015_, lean_object* v_b_1016_, lean_object* v_c_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1010_, v___x_1011_, v___x_1012_, v_inst_1013_, v_R_1014_, v_a_1015_, v_b_1016_, v_c_1017_);
lean_dec(v_b_1016_);
lean_dec_ref(v___x_1012_);
lean_dec(v___x_1011_);
lean_dec_ref(v___x_1010_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v___y_1022_; 
switch(lean_obj_tag(v_x_1019_))
{
case 2:
{
lean_object* v_info_1025_; 
v_info_1025_ = lean_ctor_get(v_x_1019_, 0);
lean_inc(v_info_1025_);
if (lean_obj_tag(v_info_1025_) == 0)
{
lean_object* v_val_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1038_; 
v_val_1026_ = lean_ctor_get(v_x_1019_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v_x_1019_, 0);
lean_dec(v_unused_1039_);
v___x_1028_ = v_x_1019_;
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_val_1026_);
lean_dec(v_x_1019_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1038_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_trailing_1030_; lean_object* v_trailStop_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v_trailing_1030_ = lean_ctor_get(v_info_1025_, 2);
lean_inc_ref(v_trailing_1030_);
v_trailStop_1031_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1030_);
lean_inc(v_trailStop_1031_);
v___x_1032_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1025_, v_a_1020_, v_trailStop_1031_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1032_);
v___x_1034_ = v___x_1028_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_val_1026_);
v___x_1034_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v_trailStop_1031_);
return v___x_1036_;
}
}
}
else
{
lean_dec_ref_known(v_x_1019_, 2);
lean_dec(v_info_1025_);
v___y_1022_ = v_a_1020_;
goto v___jp_1021_;
}
}
case 3:
{
lean_object* v_info_1040_; 
v_info_1040_ = lean_ctor_get(v_x_1019_, 0);
lean_inc(v_info_1040_);
if (lean_obj_tag(v_info_1040_) == 0)
{
lean_object* v_rawVal_1041_; lean_object* v_val_1042_; lean_object* v_preresolved_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1055_; 
v_rawVal_1041_ = lean_ctor_get(v_x_1019_, 1);
v_val_1042_ = lean_ctor_get(v_x_1019_, 2);
v_preresolved_1043_ = lean_ctor_get(v_x_1019_, 3);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_x_1019_, 0);
lean_dec(v_unused_1056_);
v___x_1045_ = v_x_1019_;
v_isShared_1046_ = v_isSharedCheck_1055_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_preresolved_1043_);
lean_inc(v_val_1042_);
lean_inc(v_rawVal_1041_);
lean_dec(v_x_1019_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1055_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_trailing_1047_; lean_object* v_trailStop_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v_trailing_1047_ = lean_ctor_get(v_info_1040_, 2);
lean_inc_ref(v_trailing_1047_);
v_trailStop_1048_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1047_);
lean_inc(v_trailStop_1048_);
v___x_1049_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1040_, v_a_1020_, v_trailStop_1048_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1049_);
v___x_1051_ = v___x_1045_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_rawVal_1041_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_val_1042_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_preresolved_1043_);
v___x_1051_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v_trailStop_1048_);
return v___x_1053_;
}
}
}
else
{
lean_dec(v_info_1040_);
lean_dec_ref_known(v_x_1019_, 4);
v___y_1022_ = v_a_1020_;
goto v___jp_1021_;
}
}
default: 
{
lean_dec(v_x_1019_);
v___y_1022_ = v_a_1020_;
goto v___jp_1021_;
}
}
v___jp_1021_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___y_1022_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
switch(lean_obj_tag(v___y_1057_))
{
case 2:
{
lean_object* v_info_1062_; 
v_info_1062_ = lean_ctor_get(v___y_1057_, 0);
lean_inc(v_info_1062_);
if (lean_obj_tag(v_info_1062_) == 0)
{
lean_object* v_val_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1075_; 
v_val_1063_ = lean_ctor_get(v___y_1057_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___y_1057_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v___y_1057_, 0);
lean_dec(v_unused_1076_);
v___x_1065_ = v___y_1057_;
v_isShared_1066_ = v_isSharedCheck_1075_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_val_1063_);
lean_dec(v___y_1057_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1075_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v_trailing_1067_; lean_object* v_trailStop_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v_trailing_1067_ = lean_ctor_get(v_info_1062_, 2);
lean_inc_ref(v_trailing_1067_);
v_trailStop_1068_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1067_);
lean_inc(v_trailStop_1068_);
v___x_1069_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1062_, v___y_1058_, v_trailStop_1068_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1069_);
v___x_1071_ = v___x_1065_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_val_1063_);
v___x_1071_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_trailStop_1068_);
return v___x_1073_;
}
}
}
else
{
lean_dec(v_info_1062_);
lean_dec_ref_known(v___y_1057_, 2);
goto v___jp_1059_;
}
}
case 3:
{
lean_object* v_info_1077_; 
v_info_1077_ = lean_ctor_get(v___y_1057_, 0);
lean_inc(v_info_1077_);
if (lean_obj_tag(v_info_1077_) == 0)
{
lean_object* v_rawVal_1078_; lean_object* v_val_1079_; lean_object* v_preresolved_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1092_; 
v_rawVal_1078_ = lean_ctor_get(v___y_1057_, 1);
v_val_1079_ = lean_ctor_get(v___y_1057_, 2);
v_preresolved_1080_ = lean_ctor_get(v___y_1057_, 3);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___y_1057_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___y_1057_, 0);
lean_dec(v_unused_1093_);
v___x_1082_ = v___y_1057_;
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_preresolved_1080_);
lean_inc(v_val_1079_);
lean_inc(v_rawVal_1078_);
lean_dec(v___y_1057_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1092_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_trailing_1084_; lean_object* v_trailStop_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v_trailing_1084_ = lean_ctor_get(v_info_1077_, 2);
lean_inc_ref(v_trailing_1084_);
v_trailStop_1085_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1084_);
lean_inc(v_trailStop_1085_);
v___x_1086_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1077_, v___y_1058_, v_trailStop_1085_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1086_);
v___x_1088_ = v___x_1082_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_rawVal_1078_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_val_1079_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_preresolved_1080_);
v___x_1088_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_trailStop_1085_);
return v___x_1090_;
}
}
}
else
{
lean_dec(v_info_1077_);
lean_dec_ref_known(v___y_1057_, 4);
goto v___jp_1059_;
}
}
default: 
{
lean_dec(v___y_1057_);
goto v___jp_1059_;
}
}
v___jp_1059_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___y_1058_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1094_, lean_object* v___y_1095_){
_start:
{
if (lean_obj_tag(v_x_1094_) == 1)
{
lean_object* v_info_1096_; lean_object* v_kind_1097_; lean_object* v_args_1098_; lean_object* v___x_1099_; lean_object* v_fst_1100_; 
v_info_1096_ = lean_ctor_get(v_x_1094_, 0);
lean_inc(v_info_1096_);
v_kind_1097_ = lean_ctor_get(v_x_1094_, 1);
lean_inc(v_kind_1097_);
v_args_1098_ = lean_ctor_get(v_x_1094_, 2);
lean_inc_ref(v_args_1098_);
v___x_1099_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1094_, v___y_1095_);
v_fst_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_fst_1100_);
if (lean_obj_tag(v_fst_1100_) == 0)
{
lean_object* v_snd_1101_; size_t v_sz_1102_; size_t v___x_1103_; lean_object* v___x_1104_; lean_object* v_fst_1105_; lean_object* v_snd_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1114_; 
v_snd_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_snd_1101_);
lean_dec_ref(v___x_1099_);
v_sz_1102_ = lean_array_size(v_args_1098_);
v___x_1103_ = ((size_t)0ULL);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1102_, v___x_1103_, v_args_1098_, v_snd_1101_);
v_fst_1105_ = lean_ctor_get(v___x_1104_, 0);
v_snd_1106_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_snd_1106_);
lean_inc(v_fst_1105_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1110_, 0, v_info_1096_);
lean_ctor_set(v___x_1110_, 1, v_kind_1097_);
lean_ctor_set(v___x_1110_, 2, v_fst_1105_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_snd_1106_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
else
{
lean_object* v_snd_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_args_1098_);
lean_dec(v_kind_1097_);
lean_dec(v_info_1096_);
v_snd_1115_ = lean_ctor_get(v___x_1099_, 1);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v___x_1099_, 0);
lean_dec(v_unused_1124_);
v___x_1117_ = v___x_1099_;
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_snd_1115_);
lean_dec(v___x_1099_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1123_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_val_1119_; lean_object* v___x_1121_; 
v_val_1119_ = lean_ctor_get(v_fst_1100_, 0);
lean_inc(v_val_1119_);
lean_dec_ref_known(v_fst_1100_, 1);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v_val_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_val_1119_);
lean_ctor_set(v_reuseFailAlloc_1122_, 1, v_snd_1115_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
else
{
lean_object* v___x_1125_; lean_object* v_fst_1126_; 
lean_inc(v_x_1094_);
v___x_1125_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1094_, v___y_1095_);
v_fst_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_fst_1126_);
if (lean_obj_tag(v_fst_1126_) == 0)
{
lean_object* v_snd_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_snd_1127_ = lean_ctor_get(v___x_1125_, 1);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1125_, 0);
lean_dec(v_unused_1135_);
v___x_1129_ = v___x_1125_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snd_1127_);
lean_dec(v___x_1125_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_x_1094_);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_x_1094_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_snd_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
else
{
lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_x_1094_);
v_snd_1136_ = lean_ctor_get(v___x_1125_, 1);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1125_, 0);
lean_dec(v_unused_1145_);
v___x_1138_ = v___x_1125_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_dec(v___x_1125_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_val_1140_; lean_object* v___x_1142_; 
v_val_1140_ = lean_ctor_get(v_fst_1126_, 0);
lean_inc(v_val_1140_);
lean_dec_ref_known(v_fst_1126_, 1);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v_val_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_val_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_snd_1136_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_bs_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_lt(v_i_1147_, v_sz_1146_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_bs_1148_);
lean_ctor_set(v___x_1151_, 1, v___y_1149_);
return v___x_1151_;
}
else
{
lean_object* v_v_1152_; lean_object* v___x_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1156_; lean_object* v_bs_x27_1157_; size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_1160_; 
v_v_1152_ = lean_array_uget_borrowed(v_bs_1148_, v_i_1147_);
lean_inc(v_v_1152_);
v___x_1153_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1152_, v___y_1149_);
v_fst_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_fst_1154_);
v_snd_1155_ = lean_ctor_get(v___x_1153_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v___x_1153_);
v___x_1156_ = lean_unsigned_to_nat(0u);
v_bs_x27_1157_ = lean_array_uset(v_bs_1148_, v_i_1147_, v___x_1156_);
v___x_1158_ = ((size_t)1ULL);
v___x_1159_ = lean_usize_add(v_i_1147_, v___x_1158_);
v___x_1160_ = lean_array_uset(v_bs_x27_1157_, v_i_1147_, v_fst_1154_);
v_i_1147_ = v___x_1159_;
v_bs_1148_ = v___x_1160_;
v___y_1149_ = v_snd_1155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1162_, lean_object* v_i_1163_, lean_object* v_bs_1164_, lean_object* v___y_1165_){
_start:
{
size_t v_sz_boxed_1166_; size_t v_i_boxed_1167_; lean_object* v_res_1168_; 
v_sz_boxed_1166_ = lean_unbox_usize(v_sz_1162_);
lean_dec(v_sz_1162_);
v_i_boxed_1167_ = lean_unbox_usize(v_i_1163_);
lean_dec(v_i_1163_);
v_res_1168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1166_, v_i_boxed_1167_, v_bs_1164_, v___y_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1169_){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_fst_1172_; 
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1169_, v___x_1170_);
v_fst_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_fst_1172_);
lean_dec_ref(v___x_1171_);
return v_fst_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1173_, lean_object* v_x_1174_){
_start:
{
switch(lean_obj_tag(v_x_1174_))
{
case 2:
{
lean_object* v_info_1175_; lean_object* v_val_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1184_; 
v_info_1175_ = lean_ctor_get(v_x_1174_, 0);
v_val_1176_ = lean_ctor_get(v_x_1174_, 1);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1178_ = v_x_1174_;
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_val_1176_);
lean_inc(v_info_1175_);
lean_dec(v_x_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1173_, v_info_1175_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_val_1176_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
case 3:
{
lean_object* v_info_1185_; lean_object* v_rawVal_1186_; lean_object* v_val_1187_; lean_object* v_preresolved_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1196_; 
v_info_1185_ = lean_ctor_get(v_x_1174_, 0);
v_rawVal_1186_ = lean_ctor_get(v_x_1174_, 1);
v_val_1187_ = lean_ctor_get(v_x_1174_, 2);
v_preresolved_1188_ = lean_ctor_get(v_x_1174_, 3);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1190_ = v_x_1174_;
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_preresolved_1188_);
lean_inc(v_val_1187_);
lean_inc(v_rawVal_1186_);
lean_inc(v_info_1185_);
lean_dec(v_x_1174_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1196_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v___x_1194_; 
v___x_1192_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1173_, v_info_1185_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1192_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_rawVal_1186_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_val_1187_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_preresolved_1188_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
case 1:
{
lean_object* v_info_1197_; lean_object* v_kind_1198_; lean_object* v_args_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_info_1197_ = lean_ctor_get(v_x_1174_, 0);
v_kind_1198_ = lean_ctor_get(v_x_1174_, 1);
v_args_1199_ = lean_ctor_get(v_x_1174_, 2);
v___x_1200_ = lean_array_get_size(v_args_1199_);
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = lean_nat_dec_eq(v___x_1200_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1214_; 
lean_inc_ref(v_args_1199_);
lean_inc(v_kind_1198_);
lean_inc(v_info_1197_);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; lean_object* v_unused_1216_; lean_object* v_unused_1217_; 
v_unused_1215_ = lean_ctor_get(v_x_1174_, 2);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_x_1174_, 1);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v_x_1174_, 0);
lean_dec(v_unused_1217_);
v___x_1204_ = v_x_1174_;
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v_x_1174_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1214_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v_i_1207_; lean_object* v___x_1208_; lean_object* v_last_1209_; lean_object* v_args_1210_; lean_object* v___x_1212_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v_i_1207_ = lean_nat_sub(v___x_1200_, v___x_1206_);
v___x_1208_ = lean_array_fget_borrowed(v_args_1199_, v_i_1207_);
lean_inc(v___x_1208_);
v_last_1209_ = l_Lean_Syntax_updateTrailing(v_trailing_1173_, v___x_1208_);
v_args_1210_ = lean_array_fset(v_args_1199_, v_i_1207_, v_last_1209_);
lean_dec(v_i_1207_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 2, v_args_1210_);
v___x_1212_ = v___x_1204_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_info_1197_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_kind_1198_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_args_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_dec_ref(v_trailing_1173_);
return v_x_1174_;
}
}
default: 
{
lean_dec_ref(v_trailing_1173_);
return v_x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_x_1218_, lean_object* v_x_1219_){
_start:
{
if (lean_obj_tag(v_x_1219_) == 0)
{
return v_x_1218_;
}
else
{
lean_object* v_head_1220_; lean_object* v_tail_1221_; lean_object* v___x_1222_; 
v_head_1220_ = lean_ctor_get(v_x_1219_, 0);
lean_inc(v_head_1220_);
v_tail_1221_ = lean_ctor_get(v_x_1219_, 1);
lean_inc(v_tail_1221_);
lean_dec_ref_known(v_x_1219_, 2);
v___x_1222_ = l_Lean_Name_append(v_x_1218_, v_head_1220_);
v_x_1218_ = v___x_1222_;
v_x_1219_ = v_tail_1221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1226_, lean_object* v_nFields_x3f_1227_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1227_) == 1)
{
lean_object* v_val_1228_; lean_object* v_nameComps_1229_; lean_object* v___x_1230_; lean_object* v_nPrefix_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_namePrefix_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_val_1228_ = lean_ctor_get(v_nFields_x3f_1227_, 0);
v_nameComps_1229_ = l_Lean_Name_components(v_n_1226_);
v___x_1230_ = l_List_lengthTR___redArg(v_nameComps_1229_);
v_nPrefix_1231_ = lean_nat_sub(v___x_1230_, v_val_1228_);
lean_dec(v___x_1230_);
v___x_1232_ = lean_box(0);
v___x_1233_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1231_);
lean_inc(v_nameComps_1229_);
v___x_1234_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1229_, v_nameComps_1229_, v_nPrefix_1231_, v___x_1233_);
v_namePrefix_1235_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1232_, v___x_1234_);
v___x_1236_ = l_List_drop___redArg(v_nPrefix_1231_, v_nameComps_1229_);
lean_dec(v_nameComps_1229_);
v___x_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_namePrefix_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
return v___x_1237_;
}
else
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Lean_Name_components(v_n_1226_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object* v_n_1239_, lean_object* v_nFields_x3f_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_n_1239_, v_nFields_x3f_1240_);
lean_dec(v_nFields_x3f_1240_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_panic_fn_borrowed(v___x_1243_, v_msg_1242_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
return v_x_1245_;
}
else
{
lean_object* v_head_1247_; lean_object* v_tail_1248_; lean_object* v_startPos_1249_; lean_object* v_stopPos_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_head_1247_ = lean_ctor_get(v_x_1246_, 0);
v_tail_1248_ = lean_ctor_get(v_x_1246_, 1);
v_startPos_1249_ = lean_ctor_get(v_head_1247_, 1);
v_stopPos_1250_ = lean_ctor_get(v_head_1247_, 2);
v___x_1251_ = lean_nat_sub(v_stopPos_1250_, v_startPos_1249_);
v___x_1252_ = lean_nat_add(v_x_1245_, v___x_1251_);
lean_dec(v___x_1251_);
lean_dec(v_x_1245_);
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = lean_nat_add(v___x_1252_, v___x_1253_);
lean_dec(v___x_1252_);
v_x_1245_ = v___x_1254_;
v_x_1246_ = v_tail_1248_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1256_, v_x_1257_);
lean_dec(v_x_1257_);
return v_res_1258_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1260_ = lean_string_utf8_byte_size(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___x_1262_);
lean_ctor_set(v___x_1264_, 2, v___x_1261_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1266_, lean_object* v_pos_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
if (lean_obj_tag(v_a_1268_) == 0)
{
lean_object* v___x_1270_; 
v___x_1270_ = l_List_reverse___redArg(v_a_1269_);
return v___x_1270_;
}
else
{
lean_object* v_head_1271_; lean_object* v_tail_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1290_; 
v_head_1271_ = lean_ctor_get(v_a_1268_, 0);
v_tail_1272_ = lean_ctor_get(v_a_1268_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_1268_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1274_ = v_a_1268_;
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_tail_1272_);
lean_inc(v_head_1271_);
lean_dec(v_a_1268_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1290_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_stopPos_1276_; lean_object* v_startPos_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_info_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v_stopPos_1276_ = lean_ctor_get(v_head_1271_, 2);
lean_inc(v_stopPos_1276_);
lean_dec(v_head_1271_);
v_startPos_1277_ = lean_ctor_get(v_rawVal_1266_, 1);
v___x_1278_ = lean_nat_sub(v_stopPos_1276_, v_startPos_1277_);
lean_dec(v_stopPos_1276_);
v___x_1279_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___x_1280_ = lean_nat_add(v___x_1278_, v_pos_1267_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_unsigned_to_nat(1u);
v___x_1282_ = lean_nat_add(v___x_1281_, v___x_1280_);
v_info_1283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1283_, 0, v___x_1279_);
lean_ctor_set(v_info_1283_, 1, v___x_1280_);
lean_ctor_set(v_info_1283_, 2, v___x_1279_);
lean_ctor_set(v_info_1283_, 3, v___x_1282_);
v___x_1284_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2));
v___x_1285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_info_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v_a_1269_);
lean_ctor_set(v___x_1274_, 0, v___x_1285_);
v___x_1287_ = v___x_1274_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_a_1269_);
v___x_1287_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
v_a_1268_ = v_tail_1272_;
v_a_1269_ = v___x_1287_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1291_, lean_object* v_pos_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1291_, v_pos_1292_, v_a_1293_, v_a_1294_);
lean_dec(v_pos_1292_);
lean_dec_ref(v_rawVal_1291_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1296_, lean_object* v_pos_1297_, lean_object* v_trailing_1298_, lean_object* v_leading_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
if (lean_obj_tag(v_a_1300_) == 0)
{
lean_object* v___x_1302_; 
lean_dec_ref(v_leading_1299_);
lean_dec_ref(v_trailing_1298_);
v___x_1302_ = l_List_reverse___redArg(v_a_1301_);
return v___x_1302_;
}
else
{
lean_object* v_head_1303_; lean_object* v_snd_1304_; lean_object* v_tail_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1335_; 
v_head_1303_ = lean_ctor_get(v_a_1300_, 0);
lean_inc(v_head_1303_);
v_snd_1304_ = lean_ctor_get(v_head_1303_, 1);
lean_inc(v_snd_1304_);
v_tail_1305_ = lean_ctor_get(v_a_1300_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_a_1300_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_a_1300_, 0);
lean_dec(v_unused_1336_);
v___x_1307_ = v_a_1300_;
v_isShared_1308_ = v_isSharedCheck_1335_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_tail_1305_);
lean_dec(v_a_1300_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1335_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_fst_1309_; lean_object* v_startPos_1310_; lean_object* v_stopPos_1311_; lean_object* v_startPos_1312_; lean_object* v_stopPos_1313_; lean_object* v_off_1314_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1329_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_fst_1309_ = lean_ctor_get(v_head_1303_, 0);
lean_inc(v_fst_1309_);
lean_dec(v_head_1303_);
v_startPos_1310_ = lean_ctor_get(v_snd_1304_, 1);
v_stopPos_1311_ = lean_ctor_get(v_snd_1304_, 2);
v_startPos_1312_ = lean_ctor_get(v_rawVal_1296_, 1);
v_stopPos_1313_ = lean_ctor_get(v_rawVal_1296_, 2);
v_off_1314_ = lean_nat_sub(v_startPos_1310_, v_startPos_1312_);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_nat_dec_eq(v_off_1314_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; 
v___x_1334_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___y_1329_ = v___x_1334_;
goto v___jp_1328_;
}
else
{
lean_inc_ref(v_leading_1299_);
v___y_1329_ = v_leading_1299_;
goto v___jp_1328_;
}
v___jp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_info_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1318_ = lean_nat_add(v_off_1314_, v_pos_1297_);
lean_dec(v_off_1314_);
v___x_1319_ = lean_nat_sub(v_stopPos_1311_, v_startPos_1310_);
v___x_1320_ = lean_nat_add(v___x_1319_, v___x_1318_);
lean_dec(v___x_1319_);
v_info_1321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1321_, 0, v___y_1316_);
lean_ctor_set(v_info_1321_, 1, v___x_1318_);
lean_ctor_set(v_info_1321_, 2, v___y_1317_);
lean_ctor_set(v_info_1321_, 3, v___x_1320_);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1323_, 0, v_info_1321_);
lean_ctor_set(v___x_1323_, 1, v_snd_1304_);
lean_ctor_set(v___x_1323_, 2, v_fst_1309_);
lean_ctor_set(v___x_1323_, 3, v___x_1322_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_a_1301_);
lean_ctor_set(v___x_1307_, 0, v___x_1323_);
v___x_1325_ = v___x_1307_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_a_1301_);
v___x_1325_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v_a_1300_ = v_tail_1305_;
v_a_1301_ = v___x_1325_;
goto _start;
}
}
v___jp_1328_:
{
uint8_t v___x_1330_; 
v___x_1330_ = lean_nat_dec_eq(v_stopPos_1311_, v_stopPos_1313_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___y_1316_ = v___y_1329_;
v___y_1317_ = v___x_1331_;
goto v___jp_1315_;
}
else
{
lean_inc_ref(v_trailing_1298_);
v___y_1316_ = v___y_1329_;
v___y_1317_ = v_trailing_1298_;
goto v___jp_1315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1337_, lean_object* v_pos_1338_, lean_object* v_trailing_1339_, lean_object* v_leading_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1337_, v_pos_1338_, v_trailing_1339_, v_leading_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_pos_1338_);
lean_dec_ref(v_rawVal_1337_);
return v_res_1343_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__5(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1352_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1353_ = lean_unsigned_to_nat(9u);
v___x_1354_ = lean_unsigned_to_nat(342u);
v___x_1355_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1356_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1357_ = l_mkPanicMessageWithDecl(v___x_1356_, v___x_1355_, v___x_1354_, v___x_1353_, v___x_1352_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1358_, lean_object* v_nFields_x3f_1359_){
_start:
{
if (lean_obj_tag(v_stx_1358_) == 3)
{
lean_object* v_info_1360_; 
v_info_1360_ = lean_ctor_get(v_stx_1358_, 0);
lean_inc(v_info_1360_);
if (lean_obj_tag(v_info_1360_) == 0)
{
lean_object* v_rawVal_1361_; lean_object* v_val_1362_; lean_object* v_leading_1363_; lean_object* v_pos_1364_; lean_object* v_trailing_1365_; lean_object* v_rawComps_1366_; uint8_t v___x_1367_; 
v_rawVal_1361_ = lean_ctor_get(v_stx_1358_, 1);
lean_inc_ref_n(v_rawVal_1361_, 2);
v_val_1362_ = lean_ctor_get(v_stx_1358_, 2);
lean_inc(v_val_1362_);
lean_dec_ref_known(v_stx_1358_, 4);
v_leading_1363_ = lean_ctor_get(v_info_1360_, 0);
lean_inc_ref(v_leading_1363_);
v_pos_1364_ = lean_ctor_get(v_info_1360_, 1);
lean_inc(v_pos_1364_);
v_trailing_1365_ = lean_ctor_get(v_info_1360_, 2);
lean_inc_ref(v_trailing_1365_);
lean_dec_ref_known(v_info_1360_, 4);
v_rawComps_1366_ = l_Lean_Syntax_splitNameLit(v_rawVal_1361_);
v___x_1367_ = l_List_isEmpty___redArg(v_rawComps_1366_);
if (v___x_1367_ == 0)
{
lean_object* v_val_1368_; lean_object* v_nameComps_1369_; lean_object* v___y_1371_; 
v_val_1368_ = l_Lean_Name_eraseMacroScopes(v_val_1362_);
lean_dec(v_val_1362_);
v_nameComps_1369_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1368_, v_nFields_x3f_1359_);
if (lean_obj_tag(v_nFields_x3f_1359_) == 1)
{
lean_object* v_val_1385_; lean_object* v_str_1386_; lean_object* v_startPos_1387_; lean_object* v_stopPos_1388_; lean_object* v___x_1389_; lean_object* v_nPrefix_1390_; lean_object* v___y_1392_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v_prefixSz_1398_; lean_object* v___x_1399_; lean_object* v_prefixSz_1400_; lean_object* v___y_1402_; uint8_t v___x_1407_; 
v_val_1385_ = lean_ctor_get(v_nFields_x3f_1359_, 0);
v_str_1386_ = lean_ctor_get(v_rawVal_1361_, 0);
v_startPos_1387_ = lean_ctor_get(v_rawVal_1361_, 1);
v_stopPos_1388_ = lean_ctor_get(v_rawVal_1361_, 2);
v___x_1389_ = l_List_lengthTR___redArg(v_rawComps_1366_);
v_nPrefix_1390_ = lean_nat_sub(v___x_1389_, v_val_1385_);
lean_dec(v___x_1389_);
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1390_);
lean_inc(v_rawComps_1366_);
v___x_1397_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1366_, v_rawComps_1366_, v_nPrefix_1390_, v___x_1396_);
v_prefixSz_1398_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1395_, v___x_1397_);
lean_dec(v___x_1397_);
v___x_1399_ = lean_unsigned_to_nat(1u);
v_prefixSz_1400_ = lean_nat_sub(v_prefixSz_1398_, v___x_1399_);
lean_dec(v_prefixSz_1398_);
v___x_1407_ = lean_nat_dec_le(v_prefixSz_1400_, v___x_1395_);
if (v___x_1407_ == 0)
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_le(v_stopPos_1388_, v_startPos_1387_);
if (v___x_1408_ == 0)
{
lean_inc(v_startPos_1387_);
v___y_1402_ = v_startPos_1387_;
goto v___jp_1401_;
}
else
{
lean_inc(v_stopPos_1388_);
v___y_1402_ = v_stopPos_1388_;
goto v___jp_1401_;
}
}
else
{
lean_object* v___x_1409_; 
lean_dec(v_prefixSz_1400_);
v___x_1409_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___y_1392_ = v___x_1409_;
goto v___jp_1391_;
}
v___jp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = l_List_drop___redArg(v_nPrefix_1390_, v_rawComps_1366_);
lean_dec(v_rawComps_1366_);
v___x_1394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___y_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___y_1371_ = v___x_1394_;
goto v___jp_1370_;
}
v___jp_1401_:
{
lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = lean_nat_add(v_startPos_1387_, v_prefixSz_1400_);
lean_dec(v_prefixSz_1400_);
v___x_1404_ = lean_nat_dec_le(v_stopPos_1388_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
lean_inc_ref(v_str_1386_);
v___x_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1405_, 0, v_str_1386_);
lean_ctor_set(v___x_1405_, 1, v___y_1402_);
lean_ctor_set(v___x_1405_, 2, v___x_1403_);
v___y_1392_ = v___x_1405_;
goto v___jp_1391_;
}
else
{
lean_object* v___x_1406_; 
lean_dec(v___x_1403_);
lean_inc(v_stopPos_1388_);
lean_inc_ref(v_str_1386_);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v_str_1386_);
lean_ctor_set(v___x_1406_, 1, v___y_1402_);
lean_ctor_set(v___x_1406_, 2, v_stopPos_1388_);
v___y_1392_ = v___x_1406_;
goto v___jp_1391_;
}
}
}
else
{
v___y_1371_ = v_rawComps_1366_;
goto v___jp_1370_;
}
v___jp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1372_ = l_List_lengthTR___redArg(v_nameComps_1369_);
v___x_1373_ = l_List_lengthTR___redArg(v___y_1371_);
v___x_1374_ = lean_nat_dec_eq(v___x_1372_, v___x_1373_);
lean_dec(v___x_1373_);
lean_dec(v___x_1372_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
lean_dec(v___y_1371_);
lean_dec(v_nameComps_1369_);
lean_dec_ref(v_trailing_1365_);
lean_dec(v_pos_1364_);
lean_dec_ref(v_leading_1363_);
lean_dec_ref(v_rawVal_1361_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_comps_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_seps_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_inc(v___y_1371_);
v___x_1376_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1369_, v___y_1371_);
v___x_1377_ = lean_box(0);
v_comps_1378_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1361_, v_pos_1364_, v_trailing_1365_, v_leading_1363_, v___x_1376_, v___x_1377_);
v___x_1379_ = lean_array_mk(v___y_1371_);
v___x_1380_ = lean_array_pop(v___x_1379_);
v___x_1381_ = lean_array_to_list(v___x_1380_);
v_seps_1382_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1361_, v_pos_1364_, v___x_1381_, v___x_1377_);
lean_dec(v_pos_1364_);
lean_dec_ref(v_rawVal_1361_);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_comps_1378_);
lean_ctor_set(v___x_1383_, 1, v_seps_1382_);
v___x_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_rawComps_1366_);
lean_dec_ref(v_trailing_1365_);
lean_dec(v_pos_1364_);
lean_dec_ref(v_leading_1363_);
lean_dec(v_val_1362_);
lean_dec_ref(v_rawVal_1361_);
v___x_1410_ = lean_box(0);
return v___x_1410_;
}
}
else
{
lean_object* v___x_1411_; 
lean_dec(v_info_1360_);
lean_dec_ref_known(v_stx_1358_, 4);
v___x_1411_ = lean_box(0);
return v___x_1411_;
}
}
else
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec(v_stx_1358_);
v___x_1412_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__5, &l_Lean_Syntax_identComponents_x3f___closed__5_once, _init_l_Lean_Syntax_identComponents_x3f___closed__5);
v___x_1413_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1412_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1414_, lean_object* v_nFields_x3f_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Syntax_identComponents_x3f(v_stx_1414_, v_nFields_x3f_1415_);
lean_dec(v_nFields_x3f_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1417_, lean_object* v_nFields_x3f_1418_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1418_) == 1)
{
lean_object* v_val_1419_; lean_object* v_nameComps_1420_; lean_object* v___x_1421_; lean_object* v_nPrefix_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v_namePrefix_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_val_1419_ = lean_ctor_get(v_nFields_x3f_1418_, 0);
v_nameComps_1420_ = l_Lean_Name_components(v_n_1417_);
v___x_1421_ = l_List_lengthTR___redArg(v_nameComps_1420_);
v_nPrefix_1422_ = lean_nat_sub(v___x_1421_, v_val_1419_);
lean_dec(v___x_1421_);
v___x_1423_ = lean_box(0);
v___x_1424_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1422_);
lean_inc(v_nameComps_1420_);
v___x_1425_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1420_, v_nameComps_1420_, v_nPrefix_1422_, v___x_1424_);
v_namePrefix_1426_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1423_, v___x_1425_);
v___x_1427_ = l_List_drop___redArg(v_nPrefix_1422_, v_nameComps_1420_);
lean_dec(v_nameComps_1420_);
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_namePrefix_1426_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
return v___x_1428_;
}
else
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Name_components(v_n_1417_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1430_, lean_object* v_nFields_x3f_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1430_, v_nFields_x3f_1431_);
lean_dec(v_nFields_x3f_1431_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_panic_fn_borrowed(v___x_1434_, v_msg_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
if (lean_obj_tag(v_a_1437_) == 0)
{
lean_object* v___x_1439_; 
lean_dec(v_info_1436_);
v___x_1439_ = l_List_reverse___redArg(v_a_1438_);
return v___x_1439_;
}
else
{
lean_object* v_head_1440_; lean_object* v_tail_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1456_; 
v_head_1440_ = lean_ctor_get(v_a_1437_, 0);
v_tail_1441_ = lean_ctor_get(v_a_1437_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1437_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1443_ = v_a_1437_;
v_isShared_1444_ = v_isSharedCheck_1456_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_tail_1441_);
lean_inc(v_head_1440_);
lean_dec(v_a_1437_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1456_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1445_ = 1;
lean_inc(v_head_1440_);
v___x_1446_ = l_Lean_Name_toString(v_head_1440_, v___x_1445_);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_string_utf8_byte_size(v___x_1446_);
v___x_1449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1446_);
lean_ctor_set(v___x_1449_, 1, v___x_1447_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
v___x_1450_ = lean_box(0);
lean_inc(v_info_1436_);
v___x_1451_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1451_, 0, v_info_1436_);
lean_ctor_set(v___x_1451_, 1, v___x_1449_);
lean_ctor_set(v___x_1451_, 2, v_head_1440_);
lean_ctor_set(v___x_1451_, 3, v___x_1450_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v_a_1438_);
lean_ctor_set(v___x_1443_, 0, v___x_1451_);
v___x_1453_ = v___x_1443_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_a_1438_);
v___x_1453_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
v_a_1437_ = v_tail_1441_;
v_a_1438_ = v___x_1453_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1458_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1459_ = lean_unsigned_to_nat(9u);
v___x_1460_ = lean_unsigned_to_nat(377u);
v___x_1461_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1462_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1463_ = l_mkPanicMessageWithDecl(v___x_1462_, v___x_1461_, v___x_1460_, v___x_1459_, v___x_1458_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1464_, lean_object* v_nFields_x3f_1465_){
_start:
{
if (lean_obj_tag(v_stx_1464_) == 3)
{
lean_object* v_info_1466_; lean_object* v_rawVal_1467_; lean_object* v_val_1468_; lean_object* v_val_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; 
v_info_1466_ = lean_ctor_get(v_stx_1464_, 0);
lean_inc(v_info_1466_);
v_rawVal_1467_ = lean_ctor_get(v_stx_1464_, 1);
v_val_1468_ = lean_ctor_get(v_stx_1464_, 2);
v_val_1469_ = l_Lean_Name_eraseMacroScopes(v_val_1468_);
v___x_1470_ = l_Lean_Name_getNumParts(v_val_1469_);
v___x_1471_ = lean_unsigned_to_nat(1u);
v___x_1472_ = lean_nat_dec_le(v___x_1470_, v___x_1471_);
lean_dec(v___x_1470_);
if (v___x_1472_ == 0)
{
if (lean_obj_tag(v_info_1466_) == 0)
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Syntax_identComponents_x3f(v_stx_1464_, v_nFields_x3f_1465_);
if (lean_obj_tag(v___x_1473_) == 1)
{
lean_object* v_val_1474_; lean_object* v_fst_1475_; 
lean_dec_ref_known(v_info_1466_, 4);
lean_dec(v_val_1469_);
v_val_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v_fst_1475_ = lean_ctor_get(v_val_1474_, 0);
lean_inc(v_fst_1475_);
lean_dec(v_val_1474_);
return v_fst_1475_;
}
else
{
lean_object* v_nameComps_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v___x_1473_);
v_nameComps_1476_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1469_, v_nFields_x3f_1465_);
v___x_1477_ = lean_box(0);
v___x_1478_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1466_, v_nameComps_1476_, v___x_1477_);
return v___x_1478_;
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec_ref_known(v_stx_1464_, 4);
v___x_1479_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1469_, v_nFields_x3f_1465_);
v___x_1480_ = lean_box(0);
v___x_1481_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1466_, v___x_1479_, v___x_1480_);
return v___x_1481_;
}
}
else
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1490_; 
lean_inc_ref(v_rawVal_1467_);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_stx_1464_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; 
v_unused_1491_ = lean_ctor_get(v_stx_1464_, 3);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_stx_1464_, 2);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_stx_1464_, 1);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_stx_1464_, 0);
lean_dec(v_unused_1494_);
v___x_1483_ = v_stx_1464_;
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v_stx_1464_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1490_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_box(0);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 3, v___x_1485_);
lean_ctor_set(v___x_1483_, 2, v_val_1469_);
v___x_1487_ = v___x_1483_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_info_1466_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_rawVal_1467_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_val_1469_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
lean_ctor_set(v___x_1488_, 1, v___x_1485_);
return v___x_1488_;
}
}
}
}
else
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec(v_stx_1464_);
v___x_1495_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1496_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1495_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1497_, lean_object* v_nFields_x3f_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Syntax_identComponents(v_stx_1497_, v_nFields_x3f_1498_);
lean_dec(v_nFields_x3f_1498_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1500_, uint8_t v_firstChoiceOnly_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1502_, 0, v_stx_1500_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*1, v_firstChoiceOnly_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1503_, lean_object* v_firstChoiceOnly_1504_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1505_; lean_object* v_res_1506_; 
v_firstChoiceOnly_boxed_1505_ = lean_unbox(v_firstChoiceOnly_1504_);
v_res_1506_ = l_Lean_Syntax_topDown(v_stx_1503_, v_firstChoiceOnly_boxed_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1507_, lean_object* v_____r_1508_, lean_object* v_b_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_b_1509_);
v___x_1511_ = lean_apply_2(v_toPure_1507_, lean_box(0), v___x_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1512_, lean_object* v_toPure_1513_, lean_object* v_____s_1514_){
_start:
{
lean_object* v_fst_1515_; 
v_fst_1515_ = lean_ctor_get(v_____s_1514_, 0);
if (lean_obj_tag(v_fst_1515_) == 0)
{
lean_object* v_snd_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v_toPure_1513_);
v_snd_1516_ = lean_ctor_get(v_____s_1514_, 1);
lean_inc(v_snd_1516_);
lean_dec_ref(v_____s_1514_);
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_apply_2(v___f_1512_, v___x_1517_, v_snd_1516_);
return v___x_1518_;
}
else
{
lean_object* v_val_1519_; lean_object* v___x_1520_; 
lean_inc_ref(v_fst_1515_);
lean_dec_ref(v_____s_1514_);
lean_dec(v___f_1512_);
v_val_1519_ = lean_ctor_get(v_fst_1515_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v_fst_1515_, 1);
v___x_1520_ = lean_apply_2(v_toPure_1513_, lean_box(0), v_val_1519_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1521_, lean_object* v_toPure_1522_, lean_object* v___x_1523_, lean_object* v_____do__lift_1524_){
_start:
{
if (lean_obj_tag(v_____do__lift_1524_) == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_____do__lift_1524_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v_snd_1521_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
v___x_1528_ = lean_apply_2(v_toPure_1522_, lean_box(0), v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v_snd_1521_);
v_a_1529_ = lean_ctor_get(v_____do__lift_1524_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_____do__lift_1524_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v_____do__lift_1524_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_____do__lift_1524_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1523_);
lean_ctor_set(v___x_1533_, 1, v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_apply_2(v_toPure_1522_, lean_box(0), v___x_1535_);
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1539_, lean_object* v___x_1540_, lean_object* v_inst_1541_, lean_object* v_f_1542_, lean_object* v_firstChoiceOnly_1543_, lean_object* v_toBind_1544_, lean_object* v_a_1545_, lean_object* v_x_1546_, lean_object* v___y_1547_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1548_; lean_object* v_res_1549_; 
v_firstChoiceOnly_boxed_1548_ = lean_unbox(v_firstChoiceOnly_1543_);
v_res_1549_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1539_, v___x_1540_, v_inst_1541_, v_f_1542_, v_firstChoiceOnly_boxed_1548_, v_toBind_1544_, v_a_1545_, v_x_1546_, v___y_1547_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1553_, lean_object* v_stx_1554_, lean_object* v_inst_1555_, lean_object* v_f_1556_, uint8_t v_firstChoiceOnly_1557_, lean_object* v_toBind_1558_, lean_object* v___f_1559_, lean_object* v___f_1560_, lean_object* v_____do__lift_1561_){
_start:
{
if (lean_obj_tag(v_____do__lift_1561_) == 0)
{
lean_object* v___x_1562_; 
lean_dec(v___f_1560_);
lean_dec(v___f_1559_);
lean_dec(v_toBind_1558_);
lean_dec(v_f_1556_);
lean_dec_ref(v_inst_1555_);
lean_dec(v_stx_1554_);
v___x_1562_ = lean_apply_2(v_toPure_1553_, lean_box(0), v_____do__lift_1561_);
return v___x_1562_;
}
else
{
if (lean_obj_tag(v_stx_1554_) == 1)
{
lean_object* v_a_1563_; lean_object* v_kind_1564_; lean_object* v_args_1565_; 
lean_dec(v___f_1560_);
v_a_1563_ = lean_ctor_get(v_____do__lift_1561_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v_____do__lift_1561_, 1);
v_kind_1564_ = lean_ctor_get(v_stx_1554_, 1);
lean_inc(v_kind_1564_);
v_args_1565_ = lean_ctor_get(v_stx_1554_, 2);
lean_inc_ref(v_args_1565_);
lean_dec_ref_known(v_stx_1554_, 3);
if (v_firstChoiceOnly_1557_ == 0)
{
lean_dec(v_kind_1564_);
goto v___jp_1566_;
}
else
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1576_ = lean_name_eq(v_kind_1564_, v___x_1575_);
lean_dec(v_kind_1564_);
if (v___x_1576_ == 0)
{
goto v___jp_1566_;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v___f_1559_);
lean_dec(v_toBind_1558_);
lean_dec(v_toPure_1553_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = lean_array_get(v___x_1577_, v_args_1565_, v___x_1578_);
lean_dec_ref(v_args_1565_);
v___x_1580_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1555_, v_f_1556_, v_firstChoiceOnly_1557_, v___x_1579_, v_a_1563_);
return v___x_1580_;
}
}
v___jp_1566_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; size_t v_sz_1571_; size_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_box(v_firstChoiceOnly_1557_);
lean_inc(v_toBind_1558_);
lean_inc_ref(v_inst_1555_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1569_, 0, v_toPure_1553_);
lean_closure_set(v___f_1569_, 1, v___x_1567_);
lean_closure_set(v___f_1569_, 2, v_inst_1555_);
lean_closure_set(v___f_1569_, 3, v_f_1556_);
lean_closure_set(v___f_1569_, 4, v___x_1568_);
lean_closure_set(v___f_1569_, 5, v_toBind_1558_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1567_);
lean_ctor_set(v___x_1570_, 1, v_a_1563_);
v_sz_1571_ = lean_array_size(v_args_1565_);
v___x_1572_ = ((size_t)0ULL);
v___x_1573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1555_, v_args_1565_, v___f_1569_, v_sz_1571_, v___x_1572_, v___x_1570_);
v___x_1574_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v___x_1573_, v___f_1559_);
return v___x_1574_;
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v___f_1559_);
lean_dec(v_toBind_1558_);
lean_dec(v_f_1556_);
lean_dec_ref(v_inst_1555_);
lean_dec(v_stx_1554_);
lean_dec(v_toPure_1553_);
v_a_1581_ = lean_ctor_get(v_____do__lift_1561_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v_____do__lift_1561_, 1);
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_apply_2(v___f_1560_, v___x_1582_, v_a_1581_);
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1584_, lean_object* v_stx_1585_, lean_object* v_inst_1586_, lean_object* v_f_1587_, lean_object* v_firstChoiceOnly_1588_, lean_object* v_toBind_1589_, lean_object* v___f_1590_, lean_object* v___f_1591_, lean_object* v_____do__lift_1592_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1593_; lean_object* v_res_1594_; 
v_firstChoiceOnly_boxed_1593_ = lean_unbox(v_firstChoiceOnly_1588_);
v_res_1594_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1584_, v_stx_1585_, v_inst_1586_, v_f_1587_, v_firstChoiceOnly_boxed_1593_, v_toBind_1589_, v___f_1590_, v___f_1591_, v_____do__lift_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1595_, lean_object* v_f_1596_, uint8_t v_firstChoiceOnly_1597_, lean_object* v_stx_1598_, lean_object* v_b_1599_){
_start:
{
lean_object* v_toApplicative_1600_; lean_object* v_toBind_1601_; lean_object* v_toPure_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; 
v_toApplicative_1600_ = lean_ctor_get(v_inst_1595_, 0);
v_toBind_1601_ = lean_ctor_get(v_inst_1595_, 1);
lean_inc_n(v_toBind_1601_, 2);
v_toPure_1602_ = lean_ctor_get(v_toApplicative_1600_, 1);
lean_inc_n(v_toPure_1602_, 3);
lean_inc(v_f_1596_);
lean_inc(v_stx_1598_);
v___x_1603_ = lean_apply_2(v_f_1596_, v_stx_1598_, v_b_1599_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1604_, 0, v_toPure_1602_);
lean_inc_ref(v___f_1604_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1605_, 0, v___f_1604_);
lean_closure_set(v___f_1605_, 1, v_toPure_1602_);
v___x_1606_ = lean_box(v_firstChoiceOnly_1597_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 9, 8);
lean_closure_set(v___f_1607_, 0, v_toPure_1602_);
lean_closure_set(v___f_1607_, 1, v_stx_1598_);
lean_closure_set(v___f_1607_, 2, v_inst_1595_);
lean_closure_set(v___f_1607_, 3, v_f_1596_);
lean_closure_set(v___f_1607_, 4, v___x_1606_);
lean_closure_set(v___f_1607_, 5, v_toBind_1601_);
lean_closure_set(v___f_1607_, 6, v___f_1605_);
lean_closure_set(v___f_1607_, 7, v___f_1604_);
v___x_1608_ = lean_apply_4(v_toBind_1601_, lean_box(0), lean_box(0), v___x_1603_, v___f_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1609_, lean_object* v___x_1610_, lean_object* v_inst_1611_, lean_object* v_f_1612_, uint8_t v_firstChoiceOnly_1613_, lean_object* v_toBind_1614_, lean_object* v_a_1615_, lean_object* v_x_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_snd_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_snd_1618_ = lean_ctor_get(v___y_1617_, 1);
lean_inc_n(v_snd_1618_, 2);
lean_dec_ref(v___y_1617_);
v___f_1619_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1619_, 0, v_snd_1618_);
lean_closure_set(v___f_1619_, 1, v_toPure_1609_);
lean_closure_set(v___f_1619_, 2, v___x_1610_);
v___x_1620_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1611_, v_f_1612_, v_firstChoiceOnly_1613_, v_a_1615_, v_snd_1618_);
v___x_1621_ = lean_apply_4(v_toBind_1614_, lean_box(0), lean_box(0), v___x_1620_, v___f_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1622_, lean_object* v_f_1623_, lean_object* v_firstChoiceOnly_1624_, lean_object* v_stx_1625_, lean_object* v_b_1626_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1627_; lean_object* v_res_1628_; 
v_firstChoiceOnly_boxed_1627_ = lean_unbox(v_firstChoiceOnly_1624_);
v_res_1628_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1622_, v_f_1623_, v_firstChoiceOnly_boxed_1627_, v_stx_1625_, v_b_1626_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1629_, lean_object* v_inst_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_f_1632_, uint8_t v_firstChoiceOnly_1633_, lean_object* v_stx_1634_, lean_object* v_b_1635_, lean_object* v_inst_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1630_, v_f_1632_, v_firstChoiceOnly_1633_, v_stx_1634_, v_b_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1638_, lean_object* v_inst_1639_, lean_object* v_00_u03b2_1640_, lean_object* v_f_1641_, lean_object* v_firstChoiceOnly_1642_, lean_object* v_stx_1643_, lean_object* v_b_1644_, lean_object* v_inst_1645_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1646_; lean_object* v_res_1647_; 
v_firstChoiceOnly_boxed_1646_ = lean_unbox(v_firstChoiceOnly_1642_);
v_res_1647_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1638_, v_inst_1639_, v_00_u03b2_1640_, v_f_1641_, v_firstChoiceOnly_boxed_1646_, v_stx_1643_, v_b_1644_, v_inst_1645_);
lean_dec(v_inst_1645_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1648_, lean_object* v_____do__lift_1649_){
_start:
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v_____do__lift_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v_____do__lift_1649_);
v___x_1651_ = lean_apply_2(v_toPure_1648_, lean_box(0), v_a_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1652_, lean_object* v_toBind_1653_, lean_object* v___f_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_x_1656_, lean_object* v_init_1657_, lean_object* v_f_1658_){
_start:
{
uint8_t v_firstChoiceOnly_1659_; lean_object* v_stx_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_firstChoiceOnly_1659_ = lean_ctor_get_uint8(v_x_1656_, sizeof(void*)*1);
v_stx_1660_ = lean_ctor_get(v_x_1656_, 0);
lean_inc(v_stx_1660_);
lean_dec_ref(v_x_1656_);
v___x_1661_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1652_, v_f_1658_, v_firstChoiceOnly_1659_, v_stx_1660_, v_init_1657_);
v___x_1662_ = lean_apply_4(v_toBind_1653_, lean_box(0), lean_box(0), v___x_1661_, v___f_1654_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1663_){
_start:
{
lean_object* v_toApplicative_1664_; lean_object* v_toBind_1665_; lean_object* v_toPure_1666_; lean_object* v___f_1667_; lean_object* v___f_1668_; 
v_toApplicative_1664_ = lean_ctor_get(v_inst_1663_, 0);
v_toBind_1665_ = lean_ctor_get(v_inst_1663_, 1);
lean_inc(v_toBind_1665_);
v_toPure_1666_ = lean_ctor_get(v_toApplicative_1664_, 1);
lean_inc(v_toPure_1666_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1667_, 0, v_toPure_1666_);
v___f_1668_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1668_, 0, v_inst_1663_);
lean_closure_set(v___f_1668_, 1, v_toBind_1665_);
lean_closure_set(v___f_1668_, 2, v___f_1667_);
return v___f_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1669_, lean_object* v_inst_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1673_, lean_object* v_val_1674_){
_start:
{
if (lean_obj_tag(v_info_1673_) == 0)
{
lean_object* v_leading_1675_; lean_object* v_trailing_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_leading_1675_ = lean_ctor_get(v_info_1673_, 0);
lean_inc_ref(v_leading_1675_);
v_trailing_1676_ = lean_ctor_get(v_info_1673_, 2);
lean_inc_ref(v_trailing_1676_);
lean_dec_ref_known(v_info_1673_, 4);
v___x_1677_ = lean_substring_tostring(v_leading_1675_);
v___x_1678_ = lean_string_append(v___x_1677_, v_val_1674_);
v___x_1679_ = lean_substring_tostring(v_trailing_1676_);
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
lean_dec_ref(v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
lean_dec(v_info_1673_);
v___x_1681_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1682_ = lean_string_append(v___x_1681_, v_val_1674_);
v___x_1683_ = lean_string_append(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1684_, lean_object* v_val_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1684_, v_val_1685_);
lean_dec_ref(v_val_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1687_, lean_object* v_as_1688_, size_t v_sz_1689_, size_t v_i_1690_, lean_object* v_b_1691_){
_start:
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_lt(v_i_1690_, v_sz_1689_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_b_1691_);
return v___x_1693_;
}
else
{
lean_object* v_snd_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1721_; 
v_snd_1694_ = lean_ctor_get(v_b_1691_, 1);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_b_1691_);
if (v_isSharedCheck_1721_ == 0)
{
lean_object* v_unused_1722_; 
v_unused_1722_ = lean_ctor_get(v_b_1691_, 0);
lean_dec(v_unused_1722_);
v___x_1696_ = v_b_1691_;
v_isShared_1697_ = v_isSharedCheck_1721_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_snd_1694_);
lean_dec(v_b_1691_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1721_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_a_1698_; lean_object* v___x_1699_; 
v_a_1698_ = lean_array_uget_borrowed(v_as_1688_, v_i_1690_);
lean_inc(v_snd_1694_);
lean_inc(v_a_1698_);
v___x_1699_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1687_, v_a_1698_, v_snd_1694_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1700_; 
lean_del_object(v___x_1696_);
lean_dec(v_snd_1694_);
v___x_1700_ = lean_box(0);
return v___x_1700_;
}
else
{
lean_object* v_val_1701_; 
v_val_1701_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_val_1701_);
if (lean_obj_tag(v_val_1701_) == 0)
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1711_; 
v_isSharedCheck_1711_ = !lean_is_exclusive(v_val_1701_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v_val_1701_, 0);
lean_dec(v_unused_1712_);
v___x_1703_ = v_val_1701_;
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_val_1701_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1699_);
v___x_1706_ = v___x_1696_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_snd_1694_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 1);
lean_ctor_set(v___x_1703_, 0, v___x_1706_);
v___x_1708_ = v___x_1703_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1699_, 1);
lean_dec(v_snd_1694_);
v_a_1713_ = lean_ctor_get(v_val_1701_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v_val_1701_, 1);
v___x_1714_ = lean_box(0);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 1, v_a_1713_);
lean_ctor_set(v___x_1696_, 0, v___x_1714_);
v___x_1716_ = v___x_1696_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_a_1713_);
v___x_1716_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
size_t v___x_1717_; size_t v___x_1718_; 
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1690_, v___x_1717_);
v_i_1690_ = v___x_1718_;
v_b_1691_ = v___x_1716_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1723_, lean_object* v_a_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v_array_1726_; lean_object* v_start_1727_; lean_object* v_stop_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1747_; 
v_array_1726_ = lean_ctor_get(v_a_1724_, 0);
v_start_1727_ = lean_ctor_get(v_a_1724_, 1);
v_stop_1728_ = lean_ctor_get(v_a_1724_, 2);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_a_1724_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1730_ = v_a_1724_;
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_stop_1728_);
lean_inc(v_start_1727_);
lean_inc(v_array_1726_);
lean_dec(v_a_1724_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_nat_dec_lt(v_start_1727_, v_stop_1728_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; 
lean_del_object(v___x_1730_);
lean_dec(v_stop_1728_);
lean_dec(v_start_1727_);
lean_dec_ref(v_array_1726_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_b_1725_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_array_fget_borrowed(v_array_1726_, v_start_1727_);
lean_inc(v___x_1734_);
v___x_1735_ = l_Lean_Syntax_reprint(v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v___x_1736_; 
lean_del_object(v___x_1730_);
lean_dec(v_stop_1728_);
lean_dec(v_start_1727_);
lean_dec_ref(v_array_1726_);
v___x_1736_ = lean_box(0);
return v___x_1736_;
}
else
{
lean_object* v_val_1737_; uint8_t v___x_1738_; 
v_val_1737_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1738_ = lean_string_dec_eq(v_val_1723_, v_val_1737_);
lean_dec(v_val_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
lean_del_object(v___x_1730_);
lean_dec(v_stop_1728_);
lean_dec(v_start_1727_);
lean_dec_ref(v_array_1726_);
v___x_1739_ = lean_box(0);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_unsigned_to_nat(1u);
v___x_1742_ = lean_nat_add(v_start_1727_, v___x_1741_);
lean_dec(v_start_1727_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v___x_1742_);
v___x_1744_ = v___x_1730_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_array_1726_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v_stop_1728_);
v___x_1744_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v_a_1724_ = v___x_1744_;
v_b_1725_ = v___x_1740_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1748_, lean_object* v_stx_1749_, lean_object* v_b_1750_){
_start:
{
lean_object* v_b_1752_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v_a_1767_; 
switch(lean_obj_tag(v_stx_1749_))
{
case 2:
{
lean_object* v_info_1777_; lean_object* v_val_1778_; lean_object* v___x_1779_; lean_object* v_s_1780_; 
v_info_1777_ = lean_ctor_get(v_stx_1749_, 0);
v_val_1778_ = lean_ctor_get(v_stx_1749_, 1);
lean_inc(v_info_1777_);
v___x_1779_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1777_, v_val_1778_);
v_s_1780_ = lean_string_append(v_b_1750_, v___x_1779_);
lean_dec_ref(v___x_1779_);
v_a_1767_ = v_s_1780_;
goto v___jp_1766_;
}
case 3:
{
lean_object* v_rawVal_1781_; lean_object* v_info_1782_; lean_object* v_str_1783_; lean_object* v_startPos_1784_; lean_object* v_stopPos_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_s_1788_; 
v_rawVal_1781_ = lean_ctor_get(v_stx_1749_, 1);
v_info_1782_ = lean_ctor_get(v_stx_1749_, 0);
v_str_1783_ = lean_ctor_get(v_rawVal_1781_, 0);
v_startPos_1784_ = lean_ctor_get(v_rawVal_1781_, 1);
v_stopPos_1785_ = lean_ctor_get(v_rawVal_1781_, 2);
v___x_1786_ = lean_string_utf8_extract(v_str_1783_, v_startPos_1784_, v_stopPos_1785_);
lean_inc(v_info_1782_);
v___x_1787_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1782_, v___x_1786_);
lean_dec_ref(v___x_1786_);
v_s_1788_ = lean_string_append(v_b_1750_, v___x_1787_);
lean_dec_ref(v___x_1787_);
v_a_1767_ = v_s_1788_;
goto v___jp_1766_;
}
case 1:
{
lean_object* v_kind_1789_; lean_object* v_args_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_kind_1789_ = lean_ctor_get(v_stx_1749_, 1);
v_args_1790_ = lean_ctor_get(v_stx_1749_, 2);
v___x_1791_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1792_ = lean_name_eq(v_kind_1789_, v___x_1791_);
if (v___x_1792_ == 0)
{
v_a_1767_ = v_b_1750_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1793_ = lean_box(0);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_array_get_borrowed(v___x_1793_, v_args_1790_, v___x_1794_);
lean_inc(v___x_1795_);
v___x_1796_ = l_Lean_Syntax_reprint(v___x_1795_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v___x_1797_; 
lean_dec_ref_known(v_stx_1749_, 3);
lean_dec_ref(v_b_1750_);
v___x_1797_ = lean_box(0);
return v___x_1797_;
}
else
{
lean_object* v_val_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_val_1798_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1798_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_array_get_size(v_args_1790_);
lean_inc_ref(v_args_1790_);
v___x_1801_ = l_Array_toSubarray___redArg(v_args_1790_, v___x_1799_, v___x_1800_);
v___x_1802_ = lean_box(0);
v___x_1803_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1798_, v___x_1801_, v___x_1802_);
lean_dec(v_val_1798_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v_stx_1749_, 3);
lean_dec_ref(v_b_1750_);
v___x_1804_ = lean_box(0);
return v___x_1804_;
}
else
{
lean_dec_ref_known(v___x_1803_, 1);
v_a_1767_ = v_b_1750_;
goto v___jp_1766_;
}
}
}
}
default: 
{
v_a_1767_ = v_b_1750_;
goto v___jp_1766_;
}
}
v___jp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_b_1752_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
v___jp_1755_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; size_t v_sz_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___y_1756_);
v_sz_1760_ = lean_array_size(v___y_1757_);
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1748_, v___y_1757_, v_sz_1760_, v___x_1761_, v___x_1759_);
lean_dec_ref(v___y_1757_);
if (lean_obj_tag(v___x_1762_) == 0)
{
return v___x_1758_;
}
else
{
lean_object* v_val_1763_; lean_object* v_fst_1764_; 
v_val_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_val_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v_fst_1764_ = lean_ctor_get(v_val_1763_, 0);
if (lean_obj_tag(v_fst_1764_) == 0)
{
lean_object* v_snd_1765_; 
v_snd_1765_ = lean_ctor_get(v_val_1763_, 1);
lean_inc(v_snd_1765_);
lean_dec(v_val_1763_);
v_b_1752_ = v_snd_1765_;
goto v___jp_1751_;
}
else
{
lean_inc_ref(v_fst_1764_);
lean_dec(v_val_1763_);
return v_fst_1764_;
}
}
}
v___jp_1766_:
{
if (lean_obj_tag(v_stx_1749_) == 1)
{
if (v_firstChoiceOnly_1748_ == 0)
{
lean_object* v_args_1768_; 
v_args_1768_ = lean_ctor_get(v_stx_1749_, 2);
lean_inc_ref(v_args_1768_);
lean_dec_ref_known(v_stx_1749_, 3);
v___y_1756_ = v_a_1767_;
v___y_1757_ = v_args_1768_;
goto v___jp_1755_;
}
else
{
lean_object* v_kind_1769_; lean_object* v_args_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_kind_1769_ = lean_ctor_get(v_stx_1749_, 1);
lean_inc(v_kind_1769_);
v_args_1770_ = lean_ctor_get(v_stx_1749_, 2);
lean_inc_ref(v_args_1770_);
lean_dec_ref_known(v_stx_1749_, 3);
v___x_1771_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1772_ = lean_name_eq(v_kind_1769_, v___x_1771_);
lean_dec(v_kind_1769_);
if (v___x_1772_ == 0)
{
v___y_1756_ = v_a_1767_;
v___y_1757_ = v_args_1770_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_array_get(v___x_1773_, v_args_1770_, v___x_1774_);
lean_dec_ref(v_args_1770_);
v_stx_1749_ = v___x_1775_;
v_b_1750_ = v_a_1767_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1749_);
v_b_1752_ = v_a_1767_;
goto v___jp_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1805_){
_start:
{
lean_object* v_s_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; 
v_s_1806_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1807_ = 1;
v___x_1808_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1807_, v_stx_1805_, v_s_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_box(0);
return v___x_1809_;
}
else
{
lean_object* v_val_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1818_; 
v_val_1810_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1812_ = v___x_1808_;
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_val_1810_);
lean_dec(v___x_1808_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_a_1814_; lean_object* v___x_1816_; 
v_a_1814_ = lean_ctor_get(v_val_1810_, 0);
lean_inc(v_a_1814_);
lean_dec(v_val_1810_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v_a_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1819_, lean_object* v_a_1820_, lean_object* v_b_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1819_, v_a_1820_, v_b_1821_);
lean_dec_ref(v_val_1819_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1823_, lean_object* v_as_1824_, lean_object* v_sz_1825_, lean_object* v_i_1826_, lean_object* v_b_1827_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1828_; size_t v_sz_boxed_1829_; size_t v_i_boxed_1830_; lean_object* v_res_1831_; 
v_firstChoiceOnly_boxed_1828_ = lean_unbox(v_firstChoiceOnly_1823_);
v_sz_boxed_1829_ = lean_unbox_usize(v_sz_1825_);
lean_dec(v_sz_1825_);
v_i_boxed_1830_ = lean_unbox_usize(v_i_1826_);
lean_dec(v_i_1826_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1828_, v_as_1824_, v_sz_boxed_1829_, v_i_boxed_1830_, v_b_1827_);
lean_dec_ref(v_as_1824_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1832_, lean_object* v_stx_1833_, lean_object* v_b_1834_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1835_; lean_object* v_res_1836_; 
v_firstChoiceOnly_boxed_1835_ = lean_unbox(v_firstChoiceOnly_1832_);
v_res_1836_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1835_, v_stx_1833_, v_b_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1837_, lean_object* v_inst_1838_, lean_object* v_R_1839_, lean_object* v_a_1840_, lean_object* v_b_1841_, lean_object* v_c_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1837_, v_a_1840_, v_b_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1844_, lean_object* v_inst_1845_, lean_object* v_R_1846_, lean_object* v_a_1847_, lean_object* v_b_1848_, lean_object* v_c_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1844_, v_inst_1845_, v_R_1846_, v_a_1847_, v_b_1848_, v_c_1849_);
lean_dec_ref(v_val_1844_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1859_, lean_object* v_stx_1860_){
_start:
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = l_Lean_Syntax_isMissing(v_stx_1860_);
if (v___x_1862_ == 0)
{
if (lean_obj_tag(v_stx_1860_) == 1)
{
lean_object* v_kind_1863_; lean_object* v_args_1864_; 
v_kind_1863_ = lean_ctor_get(v_stx_1860_, 1);
v_args_1864_ = lean_ctor_get(v_stx_1860_, 2);
if (v_firstChoiceOnly_1859_ == 0)
{
goto v___jp_1865_;
}
else
{
lean_object* v___x_1874_; uint8_t v___x_1875_; 
v___x_1874_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1875_ = lean_name_eq(v_kind_1863_, v___x_1874_);
if (v___x_1875_ == 0)
{
goto v___jp_1865_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_array_get_borrowed(v___x_1876_, v_args_1864_, v___x_1877_);
v_stx_1860_ = v___x_1878_;
goto _start;
}
}
v___jp_1865_:
{
lean_object* v___x_1866_; size_t v_sz_1867_; size_t v___x_1868_; lean_object* v___x_1869_; lean_object* v_fst_1870_; 
v___x_1866_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1867_ = lean_array_size(v_args_1864_);
v___x_1868_ = ((size_t)0ULL);
v___x_1869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1859_, v_args_1864_, v_sz_1867_, v___x_1868_, v___x_1866_);
v_fst_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_fst_1870_);
if (lean_obj_tag(v_fst_1870_) == 0)
{
lean_object* v_snd_1871_; lean_object* v___x_1872_; 
v_snd_1871_ = lean_ctor_get(v___x_1869_, 1);
lean_inc(v_snd_1871_);
lean_dec_ref(v___x_1869_);
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_snd_1871_);
return v___x_1872_;
}
else
{
lean_object* v_val_1873_; 
lean_dec_ref(v___x_1869_);
v_val_1873_ = lean_ctor_get(v_fst_1870_, 0);
lean_inc(v_val_1873_);
lean_dec_ref_known(v_fst_1870_, 1);
return v_val_1873_;
}
}
}
else
{
lean_object* v___x_1880_; 
v___x_1880_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1880_;
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1881_ = lean_box(v___x_1862_);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___x_1861_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1885_, lean_object* v_as_1886_, size_t v_sz_1887_, size_t v_i_1888_, lean_object* v_b_1889_){
_start:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_usize_dec_lt(v_i_1888_, v_sz_1887_);
if (v___x_1890_ == 0)
{
return v_b_1889_;
}
else
{
lean_object* v_snd_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1909_; 
v_snd_1891_ = lean_ctor_get(v_b_1889_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_b_1889_);
if (v_isSharedCheck_1909_ == 0)
{
lean_object* v_unused_1910_; 
v_unused_1910_ = lean_ctor_get(v_b_1889_, 0);
lean_dec(v_unused_1910_);
v___x_1893_ = v_b_1889_;
v_isShared_1894_ = v_isSharedCheck_1909_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_snd_1891_);
lean_dec(v_b_1889_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1909_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_a_1895_; lean_object* v___x_1896_; 
v_a_1895_ = lean_array_uget_borrowed(v_as_1886_, v_i_1888_);
v___x_1896_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1885_, v_a_1895_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1897_);
v___x_1899_ = v___x_1893_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_snd_1891_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
lean_dec(v_snd_1891_);
v_a_1901_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1902_ = lean_box(0);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v_a_1901_);
lean_ctor_set(v___x_1893_, 0, v___x_1902_);
v___x_1904_ = v___x_1893_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_a_1901_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
size_t v___x_1905_; size_t v___x_1906_; 
v___x_1905_ = ((size_t)1ULL);
v___x_1906_ = lean_usize_add(v_i_1888_, v___x_1905_);
v_i_1888_ = v___x_1906_;
v_b_1889_ = v___x_1904_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1911_, lean_object* v_as_1912_, lean_object* v_sz_1913_, lean_object* v_i_1914_, lean_object* v_b_1915_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1916_; size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_firstChoiceOnly_boxed_1916_ = lean_unbox(v_firstChoiceOnly_1911_);
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1913_);
lean_dec(v_sz_1913_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1914_);
lean_dec(v_i_1914_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1916_, v_as_1912_, v_sz_boxed_1917_, v_i_boxed_1918_, v_b_1915_);
lean_dec_ref(v_as_1912_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1920_, lean_object* v_stx_1921_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1922_; lean_object* v_res_1923_; 
v_firstChoiceOnly_boxed_1922_ = lean_unbox(v_firstChoiceOnly_1920_);
v_res_1923_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1922_, v_stx_1921_);
lean_dec(v_stx_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1924_){
_start:
{
uint8_t v___x_1925_; lean_object* v___y_1927_; lean_object* v___x_1931_; lean_object* v_a_1932_; 
v___x_1925_ = 0;
v___x_1931_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1925_, v_stx_1924_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___y_1927_ = v_a_1932_;
goto v___jp_1926_;
v___jp_1926_:
{
lean_object* v_fst_1928_; 
v_fst_1928_ = lean_ctor_get(v___y_1927_, 0);
lean_inc(v_fst_1928_);
lean_dec_ref(v___y_1927_);
if (lean_obj_tag(v_fst_1928_) == 0)
{
return v___x_1925_;
}
else
{
lean_object* v_val_1929_; uint8_t v___x_1930_; 
v_val_1929_ = lean_ctor_get(v_fst_1928_, 0);
lean_inc(v_val_1929_);
lean_dec_ref_known(v_fst_1928_, 1);
v___x_1930_ = lean_unbox(v_val_1929_);
lean_dec(v_val_1929_);
return v___x_1930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1933_){
_start:
{
uint8_t v_res_1934_; lean_object* v_r_1935_; 
v_res_1934_ = l_Lean_Syntax_hasMissing(v_stx_1933_);
lean_dec(v_stx_1933_);
v_r_1935_ = lean_box(v_res_1934_);
return v_r_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1936_, lean_object* v_stx_1937_, lean_object* v_b_1938_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1936_, v_stx_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1940_, lean_object* v_stx_1941_, lean_object* v_b_1942_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1943_; lean_object* v_res_1944_; 
v_firstChoiceOnly_boxed_1943_ = lean_unbox(v_firstChoiceOnly_1940_);
v_res_1944_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1943_, v_stx_1941_, v_b_1942_);
lean_dec_ref(v_b_1942_);
lean_dec(v_stx_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1945_, uint8_t v_canonicalOnly_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Syntax_getPos_x3f(v_stx_1945_, v_canonicalOnly_1946_);
if (lean_obj_tag(v___x_1947_) == 1)
{
lean_object* v_val_1948_; lean_object* v___x_1949_; 
v_val_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_val_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1945_, v_canonicalOnly_1946_);
if (lean_obj_tag(v___x_1949_) == 1)
{
lean_object* v_val_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1958_; 
v_val_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_val_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1958_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v_val_1948_);
lean_ctor_set(v___x_1954_, 1, v_val_1950_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1954_);
v___x_1956_ = v___x_1952_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
else
{
lean_object* v___x_1959_; 
lean_dec(v___x_1949_);
lean_dec(v_val_1948_);
v___x_1959_ = lean_box(0);
return v___x_1959_;
}
}
else
{
lean_object* v___x_1960_; 
lean_dec(v___x_1947_);
v___x_1960_ = lean_box(0);
return v___x_1960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1961_, lean_object* v_canonicalOnly_1962_){
_start:
{
uint8_t v_canonicalOnly_boxed_1963_; lean_object* v_res_1964_; 
v_canonicalOnly_boxed_1963_ = lean_unbox(v_canonicalOnly_1962_);
v_res_1964_ = l_Lean_Syntax_getRange_x3f(v_stx_1961_, v_canonicalOnly_boxed_1963_);
lean_dec(v_stx_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1965_, uint8_t v_canonicalOnly_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_Syntax_getPos_x3f(v_stx_1965_, v_canonicalOnly_1966_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_box(0);
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1970_; 
v_val_1969_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1970_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1965_, v_canonicalOnly_1966_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; 
lean_dec(v_val_1969_);
v___x_1971_ = lean_box(0);
return v___x_1971_;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1980_; 
v_val_1972_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1974_ = v___x_1970_;
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v___x_1970_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1980_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_val_1969_);
lean_ctor_set(v___x_1976_, 1, v_val_1972_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1976_);
v___x_1978_ = v___x_1974_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1981_, lean_object* v_canonicalOnly_1982_){
_start:
{
uint8_t v_canonicalOnly_boxed_1983_; lean_object* v_res_1984_; 
v_canonicalOnly_boxed_1983_ = lean_unbox(v_canonicalOnly_1982_);
v_res_1984_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1981_, v_canonicalOnly_boxed_1983_);
lean_dec(v_stx_1981_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_1985_, uint8_t v_canonical_1986_){
_start:
{
lean_object* v_start_1987_; lean_object* v_stop_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1997_; 
v_start_1987_ = lean_ctor_get(v_range_1985_, 0);
v_stop_1988_ = lean_ctor_get(v_range_1985_, 1);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_range_1985_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1990_ = v_range_1985_;
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_stop_1988_);
lean_inc(v_start_1987_);
lean_dec(v_range_1985_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1997_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1992_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1992_, 0, v_start_1987_);
lean_ctor_set(v___x_1992_, 1, v_stop_1988_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*2, v_canonical_1986_);
v___x_1993_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_1991_ == 0)
{
lean_ctor_set_tag(v___x_1990_, 2);
lean_ctor_set(v___x_1990_, 1, v___x_1993_);
lean_ctor_set(v___x_1990_, 0, v___x_1992_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_1998_, lean_object* v_canonical_1999_){
_start:
{
uint8_t v_canonical_boxed_2000_; lean_object* v_res_2001_; 
v_canonical_boxed_2000_ = lean_unbox(v_canonical_1999_);
v_res_2001_ = l_Lean_Syntax_ofRange(v_range_1998_, v_canonical_boxed_2000_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2005_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2006_, 0, v_stx_2004_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
lean_ctor_set(v___x_2006_, 2, v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2007_, lean_object* v_stx_2008_){
_start:
{
lean_object* v_parents_2009_; lean_object* v_idxs_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_parents_2009_ = lean_ctor_get(v_t_2007_, 1);
v_idxs_2010_ = lean_ctor_get(v_t_2007_, 2);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_t_2007_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v_t_2007_, 0);
lean_dec(v_unused_2018_);
v___x_2012_ = v_t_2007_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_idxs_2010_);
lean_inc(v_parents_2009_);
lean_dec(v_t_2007_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v_stx_2008_);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_stx_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_parents_2009_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_idxs_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2019_, lean_object* v_idx_2020_){
_start:
{
lean_object* v_cur_2021_; lean_object* v_parents_2022_; lean_object* v_idxs_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2043_; 
v_cur_2021_ = lean_ctor_get(v_t_2019_, 0);
v_parents_2022_ = lean_ctor_get(v_t_2019_, 1);
v_idxs_2023_ = lean_ctor_get(v_t_2019_, 2);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_t_2019_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2025_ = v_t_2019_;
v_isShared_2026_ = v_isSharedCheck_2043_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_idxs_2023_);
lean_inc(v_parents_2022_);
lean_inc(v_cur_2021_);
lean_dec(v_t_2019_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2043_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = l_Lean_Syntax_getNumArgs(v_cur_2021_);
v___x_2028_ = lean_nat_dec_lt(v_idx_2020_, v___x_2027_);
lean_dec(v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_array_push(v_parents_2022_, v_cur_2021_);
v___x_2031_ = lean_array_push(v_idxs_2023_, v_idx_2020_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 2, v___x_2031_);
lean_ctor_set(v___x_2025_, 1, v___x_2030_);
lean_ctor_set(v___x_2025_, 0, v___x_2029_);
v___x_2033_ = v___x_2025_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2035_ = l_Lean_Syntax_getArg(v_cur_2021_, v_idx_2020_);
v___x_2036_ = lean_box(0);
v___x_2037_ = l_Lean_Syntax_setArg(v_cur_2021_, v_idx_2020_, v___x_2036_);
v___x_2038_ = lean_array_push(v_parents_2022_, v___x_2037_);
v___x_2039_ = lean_array_push(v_idxs_2023_, v_idx_2020_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 2, v___x_2039_);
lean_ctor_set(v___x_2025_, 1, v___x_2038_);
lean_ctor_set(v___x_2025_, 0, v___x_2035_);
v___x_2041_ = v___x_2025_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2044_){
_start:
{
lean_object* v_cur_2045_; lean_object* v_parents_2046_; lean_object* v_idxs_2047_; lean_object* v___y_2049_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_cur_2045_ = lean_ctor_get(v_t_2044_, 0);
v_parents_2046_ = lean_ctor_get(v_t_2044_, 1);
v_idxs_2047_ = lean_ctor_get(v_t_2044_, 2);
v___x_2053_ = lean_unsigned_to_nat(0u);
v___x_2054_ = lean_array_get_size(v_parents_2046_);
v___x_2055_ = lean_nat_dec_lt(v___x_2053_, v___x_2054_);
if (v___x_2055_ == 0)
{
return v_t_2044_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
lean_inc_ref(v_idxs_2047_);
lean_inc_ref(v_parents_2046_);
lean_inc(v_cur_2045_);
lean_dec_ref(v_t_2044_);
v___x_2056_ = lean_array_get_size(v_idxs_2047_);
v___x_2057_ = lean_unsigned_to_nat(1u);
v___x_2058_ = lean_nat_sub(v___x_2056_, v___x_2057_);
v___x_2059_ = lean_array_get_borrowed(v___x_2053_, v_idxs_2047_, v___x_2058_);
lean_dec(v___x_2058_);
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_nat_sub(v___x_2054_, v___x_2057_);
v___x_2062_ = lean_array_get_borrowed(v___x_2060_, v_parents_2046_, v___x_2061_);
lean_dec(v___x_2061_);
v___x_2063_ = l_Lean_Syntax_getNumArgs(v___x_2062_);
v___x_2064_ = lean_nat_dec_lt(v___x_2059_, v___x_2063_);
lean_dec(v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec(v_cur_2045_);
lean_inc(v___x_2062_);
v___y_2049_ = v___x_2062_;
goto v___jp_2048_;
}
else
{
lean_object* v___x_2065_; 
lean_inc(v___x_2062_);
v___x_2065_ = l_Lean_Syntax_setArg(v___x_2062_, v___x_2059_, v_cur_2045_);
v___y_2049_ = v___x_2065_;
goto v___jp_2048_;
}
}
v___jp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = lean_array_pop(v_parents_2046_);
v___x_2051_ = lean_array_pop(v_idxs_2047_);
v___x_2052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2052_, 0, v___y_2049_);
lean_ctor_set(v___x_2052_, 1, v___x_2050_);
lean_ctor_set(v___x_2052_, 2, v___x_2051_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2066_){
_start:
{
lean_object* v_parents_2067_; lean_object* v_idxs_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v_parents_2067_ = lean_ctor_get(v_t_2066_, 1);
v_idxs_2068_ = lean_ctor_get(v_t_2066_, 2);
v___x_2069_ = lean_unsigned_to_nat(0u);
v___x_2070_ = lean_array_get_size(v_parents_2067_);
v___x_2071_ = lean_nat_dec_lt(v___x_2069_, v___x_2070_);
if (v___x_2071_ == 0)
{
return v_t_2066_;
}
else
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_inc_ref(v_idxs_2068_);
v___x_2072_ = l_Lean_Syntax_Traverser_up(v_t_2066_);
v___x_2073_ = lean_array_get_size(v_idxs_2068_);
v___x_2074_ = lean_unsigned_to_nat(1u);
v___x_2075_ = lean_nat_sub(v___x_2073_, v___x_2074_);
v___x_2076_ = lean_array_get(v___x_2069_, v_idxs_2068_, v___x_2075_);
lean_dec(v___x_2075_);
lean_dec_ref(v_idxs_2068_);
v___x_2077_ = lean_nat_sub(v___x_2076_, v___x_2074_);
lean_dec(v___x_2076_);
v___x_2078_ = l_Lean_Syntax_Traverser_down(v___x_2072_, v___x_2077_);
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2079_){
_start:
{
lean_object* v_parents_2080_; lean_object* v_idxs_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_parents_2080_ = lean_ctor_get(v_t_2079_, 1);
v_idxs_2081_ = lean_ctor_get(v_t_2079_, 2);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_array_get_size(v_parents_2080_);
v___x_2084_ = lean_nat_dec_lt(v___x_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
return v_t_2079_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_inc_ref(v_idxs_2081_);
v___x_2085_ = l_Lean_Syntax_Traverser_up(v_t_2079_);
v___x_2086_ = lean_array_get_size(v_idxs_2081_);
v___x_2087_ = lean_unsigned_to_nat(1u);
v___x_2088_ = lean_nat_sub(v___x_2086_, v___x_2087_);
v___x_2089_ = lean_array_get(v___x_2082_, v_idxs_2081_, v___x_2088_);
lean_dec(v___x_2088_);
lean_dec_ref(v_idxs_2081_);
v___x_2090_ = lean_nat_add(v___x_2089_, v___x_2087_);
lean_dec(v___x_2089_);
v___x_2091_ = l_Lean_Syntax_Traverser_down(v___x_2085_, v___x_2090_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2092_){
_start:
{
lean_object* v_cur_2093_; 
v_cur_2093_ = lean_ctor_get(v_self_2092_, 0);
lean_inc(v_cur_2093_);
return v_cur_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2094_);
lean_dec_ref(v_self_2094_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2097_, lean_object* v_t_2098_){
_start:
{
lean_object* v_toApplicative_2099_; lean_object* v_toFunctor_2100_; lean_object* v_map_2101_; lean_object* v_get_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; 
v_toApplicative_2099_ = lean_ctor_get(v_inst_2097_, 0);
lean_inc_ref(v_toApplicative_2099_);
lean_dec_ref(v_inst_2097_);
v_toFunctor_2100_ = lean_ctor_get(v_toApplicative_2099_, 0);
lean_inc_ref(v_toFunctor_2100_);
lean_dec_ref(v_toApplicative_2099_);
v_map_2101_ = lean_ctor_get(v_toFunctor_2100_, 0);
lean_inc(v_map_2101_);
lean_dec_ref(v_toFunctor_2100_);
v_get_2102_ = lean_ctor_get(v_t_2098_, 0);
lean_inc(v_get_2102_);
lean_dec_ref(v_t_2098_);
v___f_2103_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2104_ = lean_apply_4(v_map_2101_, lean_box(0), lean_box(0), v___f_2103_, v_get_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2105_, lean_object* v_inst_2106_, lean_object* v_t_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2106_, v_t_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2109_, lean_object* v_s_2110_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_box(0);
v___x_2112_ = l_Lean_Syntax_Traverser_setCur(v_s_2110_, v_stx_2109_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2114_, lean_object* v_stx_2115_){
_start:
{
lean_object* v_modifyGet_2116_; lean_object* v___f_2117_; lean_object* v___x_2118_; 
v_modifyGet_2116_ = lean_ctor_get(v_t_2114_, 2);
lean_inc(v_modifyGet_2116_);
lean_dec_ref(v_t_2114_);
v___f_2117_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2117_, 0, v_stx_2115_);
v___x_2118_ = lean_apply_2(v_modifyGet_2116_, lean_box(0), v___f_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2119_, lean_object* v_t_2120_, lean_object* v_stx_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2120_, v_stx_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2123_, lean_object* v_s_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_box(0);
v___x_2126_ = l_Lean_Syntax_Traverser_down(v_s_2124_, v_idx_2123_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2128_, lean_object* v_idx_2129_){
_start:
{
lean_object* v_modifyGet_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; 
v_modifyGet_2130_ = lean_ctor_get(v_t_2128_, 2);
lean_inc(v_modifyGet_2130_);
lean_dec_ref(v_t_2128_);
v___f_2131_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2131_, 0, v_idx_2129_);
v___x_2132_ = lean_apply_2(v_modifyGet_2130_, lean_box(0), v___f_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2133_, lean_object* v_t_2134_, lean_object* v_idx_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2134_, v_idx_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2137_){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = lean_box(0);
v___x_2139_ = l_Lean_Syntax_Traverser_up(v_s_2137_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2142_){
_start:
{
lean_object* v_modifyGet_2143_; lean_object* v___f_2144_; lean_object* v___x_2145_; 
v_modifyGet_2143_ = lean_ctor_get(v_t_2142_, 2);
lean_inc(v_modifyGet_2143_);
lean_dec_ref(v_t_2142_);
v___f_2144_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2145_ = lean_apply_2(v_modifyGet_2143_, lean_box(0), v___f_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2146_, lean_object* v_t_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2149_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = l_Lean_Syntax_Traverser_left(v_s_2149_);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2154_){
_start:
{
lean_object* v_modifyGet_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; 
v_modifyGet_2155_ = lean_ctor_get(v_t_2154_, 2);
lean_inc(v_modifyGet_2155_);
lean_dec_ref(v_t_2154_);
v___f_2156_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2157_ = lean_apply_2(v_modifyGet_2155_, lean_box(0), v___f_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2158_, lean_object* v_t_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2161_){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = l_Lean_Syntax_Traverser_right(v_s_2161_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2166_){
_start:
{
lean_object* v_modifyGet_2167_; lean_object* v___f_2168_; lean_object* v___x_2169_; 
v_modifyGet_2167_ = lean_ctor_get(v_t_2166_, 2);
lean_inc(v_modifyGet_2167_);
lean_dec_ref(v_t_2166_);
v___f_2168_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2169_ = lean_apply_2(v_modifyGet_2167_, lean_box(0), v___f_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2170_, lean_object* v_t_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2173_, lean_object* v_st_2174_){
_start:
{
lean_object* v_idxs_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v_idxs_2175_ = lean_ctor_get(v_st_2174_, 2);
v___x_2176_ = lean_array_get_size(v_idxs_2175_);
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = lean_nat_sub(v___x_2176_, v___x_2177_);
v___x_2179_ = lean_nat_dec_lt(v___x_2178_, v___x_2176_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_dec(v___x_2178_);
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_apply_2(v_toPure_2173_, lean_box(0), v___x_2180_);
return v___x_2181_;
}
else
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_array_fget_borrowed(v_idxs_2175_, v___x_2178_);
lean_dec(v___x_2178_);
lean_inc(v___x_2182_);
v___x_2183_ = lean_apply_2(v_toPure_2173_, lean_box(0), v___x_2182_);
return v___x_2183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2184_, lean_object* v_st_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2184_, v_st_2185_);
lean_dec_ref(v_st_2185_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2187_, lean_object* v_t_2188_){
_start:
{
lean_object* v_toApplicative_2189_; lean_object* v_toBind_2190_; lean_object* v_get_2191_; lean_object* v_toPure_2192_; lean_object* v___f_2193_; lean_object* v___x_2194_; 
v_toApplicative_2189_ = lean_ctor_get(v_inst_2187_, 0);
lean_inc_ref(v_toApplicative_2189_);
v_toBind_2190_ = lean_ctor_get(v_inst_2187_, 1);
lean_inc(v_toBind_2190_);
lean_dec_ref(v_inst_2187_);
v_get_2191_ = lean_ctor_get(v_t_2188_, 0);
lean_inc(v_get_2191_);
lean_dec_ref(v_t_2188_);
v_toPure_2192_ = lean_ctor_get(v_toApplicative_2189_, 1);
lean_inc(v_toPure_2192_);
lean_dec_ref(v_toApplicative_2189_);
v___f_2193_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2193_, 0, v_toPure_2192_);
v___x_2194_ = lean_apply_4(v_toBind_2190_, lean_box(0), lean_box(0), v_get_2191_, v___f_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2195_, lean_object* v_inst_2196_, lean_object* v_t_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2196_, v_t_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2199_, lean_object* v_i_2200_){
_start:
{
lean_object* v_args_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_args_2201_ = lean_ctor_get(v_n_2199_, 2);
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_array_get_borrowed(v___x_2202_, v_args_2201_, v_i_2200_);
v___x_2204_ = l_Lean_Syntax_getId(v___x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2205_, lean_object* v_i_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_SyntaxNode_getIdAt(v_n_2205_, v_i_2206_);
lean_dec(v_i_2206_);
lean_dec(v_n_2205_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2208_){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2210_ = lean_box(2);
v___x_2211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
lean_ctor_set(v___x_2211_, 2, v_args_2208_);
return v___x_2211_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2217_){
_start:
{
if (lean_obj_tag(v_x_2217_) == 1)
{
lean_object* v_kind_2218_; 
v_kind_2218_ = lean_ctor_get(v_x_2217_, 1);
if (lean_obj_tag(v_kind_2218_) == 1)
{
lean_object* v_pre_2219_; lean_object* v_str_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_pre_2219_ = lean_ctor_get(v_kind_2218_, 0);
v_str_2220_ = lean_ctor_get(v_kind_2218_, 1);
v___x_2221_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2222_ = lean_string_dec_eq(v_str_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2224_ = lean_string_dec_eq(v_str_2220_, v___x_2223_);
if (v___x_2224_ == 0)
{
return v___x_2224_;
}
else
{
if (lean_obj_tag(v_pre_2219_) == 1)
{
lean_object* v_pre_2225_; 
v_pre_2225_ = lean_ctor_get(v_pre_2219_, 0);
if (lean_obj_tag(v_pre_2225_) == 1)
{
lean_object* v_pre_2226_; 
v_pre_2226_ = lean_ctor_get(v_pre_2225_, 0);
if (lean_obj_tag(v_pre_2226_) == 1)
{
lean_object* v_pre_2227_; 
v_pre_2227_ = lean_ctor_get(v_pre_2226_, 0);
if (lean_obj_tag(v_pre_2227_) == 0)
{
lean_object* v_str_2228_; lean_object* v_str_2229_; lean_object* v_str_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v_str_2228_ = lean_ctor_get(v_pre_2219_, 1);
v_str_2229_ = lean_ctor_get(v_pre_2225_, 1);
v_str_2230_ = lean_ctor_get(v_pre_2226_, 1);
v___x_2231_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2232_ = lean_string_dec_eq(v_str_2230_, v___x_2231_);
if (v___x_2232_ == 0)
{
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2234_ = lean_string_dec_eq(v_str_2229_, v___x_2233_);
if (v___x_2234_ == 0)
{
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___x_2235_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2236_ = lean_string_dec_eq(v_str_2228_, v___x_2235_);
return v___x_2236_;
}
}
}
else
{
return v___x_2222_;
}
}
else
{
return v___x_2222_;
}
}
else
{
return v___x_2222_;
}
}
else
{
return v___x_2222_;
}
}
}
else
{
return v___x_2222_;
}
}
else
{
uint8_t v___x_2237_; 
v___x_2237_ = 0;
return v___x_2237_;
}
}
else
{
uint8_t v___x_2238_; 
v___x_2238_ = 0;
return v___x_2238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2239_){
_start:
{
uint8_t v_res_2240_; lean_object* v_r_2241_; 
v_res_2240_ = l_Lean_Syntax_isQuot(v_x_2239_);
lean_dec(v_x_2239_);
v_r_2241_ = lean_box(v_res_2240_);
return v_r_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___y_2251_; uint8_t v___x_2257_; 
v___x_2248_ = l_Lean_Syntax_getNumArgs(v_stx_2247_);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_dec_eq(v___x_2248_, v___x_2249_);
lean_dec(v___x_2248_);
if (v___x_2257_ == 0)
{
v___y_2251_ = v_stx_2247_;
goto v___jp_2250_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = l_Lean_Syntax_getArg(v_stx_2247_, v___x_2258_);
lean_dec(v_stx_2247_);
v___y_2251_ = v___x_2259_;
goto v___jp_2250_;
}
v___jp_2250_:
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2251_);
v___x_2253_ = l_Lean_Syntax_isOfKind(v___y_2251_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Syntax_getArg(v___y_2251_, v___x_2249_);
lean_dec(v___y_2251_);
return v___x_2254_;
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(3u);
v___x_2256_ = l_Lean_Syntax_getArg(v___y_2251_, v___x_2255_);
lean_dec(v___y_2251_);
return v___x_2256_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2261_){
_start:
{
if (lean_obj_tag(v_x_2261_) == 1)
{
lean_object* v_kind_2262_; 
v_kind_2262_ = lean_ctor_get(v_x_2261_, 1);
if (lean_obj_tag(v_kind_2262_) == 1)
{
lean_object* v_str_2263_; lean_object* v___x_2264_; uint8_t v___x_2265_; 
v_str_2263_ = lean_ctor_get(v_kind_2262_, 1);
v___x_2264_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2265_ = lean_string_dec_eq(v_str_2263_, v___x_2264_);
return v___x_2265_;
}
else
{
uint8_t v___x_2266_; 
v___x_2266_ = 0;
return v___x_2266_;
}
}
else
{
uint8_t v___x_2267_; 
v___x_2267_ = 0;
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2268_){
_start:
{
uint8_t v_res_2269_; lean_object* v_r_2270_; 
v_res_2269_ = l_Lean_Syntax_isAntiquot(v_x_2268_);
lean_dec(v_x_2268_);
v_r_2270_ = lean_box(v_res_2269_);
return v_r_2270_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t v___y_2271_, uint8_t v___x_2272_, lean_object* v_as_2273_, size_t v_i_2274_, size_t v_stop_2275_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_usize_dec_eq(v_i_2274_, v_stop_2275_);
if (v___x_2276_ == 0)
{
uint8_t v___x_2277_; uint8_t v___y_2279_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2277_ = 1;
v___x_2283_ = lean_array_uget_borrowed(v_as_2273_, v_i_2274_);
v___x_2284_ = l_Lean_Syntax_isAntiquot(v___x_2283_);
if (v___x_2284_ == 0)
{
v___y_2279_ = v___y_2271_;
goto v___jp_2278_;
}
else
{
v___y_2279_ = v___x_2272_;
goto v___jp_2278_;
}
v___jp_2278_:
{
if (v___y_2279_ == 0)
{
size_t v___x_2280_; size_t v___x_2281_; 
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_add(v_i_2274_, v___x_2280_);
v_i_2274_ = v___x_2281_;
goto _start;
}
else
{
return v___x_2277_;
}
}
}
else
{
uint8_t v___x_2285_; 
v___x_2285_ = 0;
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___y_2286_, lean_object* v___x_2287_, lean_object* v_as_2288_, lean_object* v_i_2289_, lean_object* v_stop_2290_){
_start:
{
uint8_t v___y_340__boxed_2291_; uint8_t v___x_341__boxed_2292_; size_t v_i_boxed_2293_; size_t v_stop_boxed_2294_; uint8_t v_res_2295_; lean_object* v_r_2296_; 
v___y_340__boxed_2291_ = lean_unbox(v___y_2286_);
v___x_341__boxed_2292_ = lean_unbox(v___x_2287_);
v_i_boxed_2293_ = lean_unbox_usize(v_i_2289_);
lean_dec(v_i_2289_);
v_stop_boxed_2294_ = lean_unbox_usize(v_stop_2290_);
lean_dec(v_stop_2290_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_340__boxed_2291_, v___x_341__boxed_2292_, v_as_2288_, v_i_boxed_2293_, v_stop_boxed_2294_);
lean_dec_ref(v_as_2288_);
v_r_2296_ = lean_box(v_res_2295_);
return v_r_2296_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2297_){
_start:
{
uint8_t v___x_2298_; uint8_t v___y_2300_; 
v___x_2298_ = l_Lean_Syntax_isAntiquot(v_stx_2297_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2308_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2297_);
v___x_2309_ = l_Lean_Syntax_isOfKind(v_stx_2297_, v___x_2308_);
if (v___x_2309_ == 0)
{
v___y_2300_ = v___x_2309_;
goto v___jp_2299_;
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = l_Lean_Syntax_getNumArgs(v_stx_2297_);
v___x_2312_ = lean_nat_dec_lt(v___x_2310_, v___x_2311_);
lean_dec(v___x_2311_);
v___y_2300_ = v___x_2312_;
goto v___jp_2299_;
}
}
else
{
lean_dec(v_stx_2297_);
return v___x_2298_;
}
v___jp_2299_:
{
if (v___y_2300_ == 0)
{
lean_dec(v_stx_2297_);
return v___y_2300_;
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2301_ = l_Lean_Syntax_getArgs(v_stx_2297_);
lean_dec(v_stx_2297_);
v___x_2302_ = lean_unsigned_to_nat(0u);
v___x_2303_ = lean_array_get_size(v___x_2301_);
v___x_2304_ = lean_nat_dec_lt(v___x_2302_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_dec_ref(v___x_2301_);
return v___y_2300_;
}
else
{
if (v___x_2304_ == 0)
{
lean_dec_ref(v___x_2301_);
return v___y_2300_;
}
else
{
size_t v___x_2305_; size_t v___x_2306_; uint8_t v___x_2307_; 
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = lean_usize_of_nat(v___x_2303_);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2300_, v___x_2298_, v___x_2301_, v___x_2305_, v___x_2306_);
lean_dec_ref(v___x_2301_);
if (v___x_2307_ == 0)
{
return v___y_2300_;
}
else
{
return v___x_2298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2313_){
_start:
{
uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_res_2314_ = l_Lean_Syntax_isAntiquots(v_stx_2313_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2316_){
_start:
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2316_);
v___x_2318_ = l_Lean_Syntax_isOfKind(v_stx_2316_, v___x_2317_);
if (v___x_2318_ == 0)
{
return v_stx_2316_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = l_Lean_Syntax_getArg(v_stx_2316_, v___x_2319_);
lean_dec(v_stx_2316_);
return v___x_2320_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2323_ = l_Lean_mkAtom(v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2326_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2327_ = lean_unsigned_to_nat(4u);
v___x_2328_ = lean_mk_empty_array_with_capacity(v___x_2327_);
v___x_2329_ = lean_array_push(v___x_2328_, v___x_2326_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2338_ = l_Lean_mkAtom(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2340_ = lean_unsigned_to_nat(2u);
v___x_2341_ = lean_mk_empty_array_with_capacity(v___x_2340_);
v___x_2342_ = lean_array_push(v___x_2341_, v___x_2339_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2354_ = l_Lean_mkAtom(v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2357_ = l_Lean_mkAtom(v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2358_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2359_ = lean_unsigned_to_nat(3u);
v___x_2360_ = lean_mk_empty_array_with_capacity(v___x_2359_);
v___x_2361_ = lean_array_push(v___x_2360_, v___x_2358_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2362_, lean_object* v_term_2363_, lean_object* v_nesting_2364_, lean_object* v_name_2365_, uint8_t v_isPseudoKind_2366_){
_start:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_nesting_2371_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2390_; uint8_t v___x_2398_; 
v___x_2367_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2368_ = lean_mk_array(v_nesting_2364_, v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2370_ = lean_box(2);
v_nesting_2371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2371_, 0, v___x_2370_);
lean_ctor_set(v_nesting_2371_, 1, v___x_2369_);
lean_ctor_set(v_nesting_2371_, 2, v___x_2368_);
v___x_2398_ = l_Lean_Syntax_isIdent(v_term_2363_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2363_);
v___x_2400_ = l_Lean_Syntax_isOfKind(v_term_2363_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2401_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2402_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2403_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2404_ = lean_array_push(v___x_2403_, v_term_2363_);
v___x_2405_ = lean_array_push(v___x_2404_, v___x_2402_);
v___x_2406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2370_);
lean_ctor_set(v___x_2406_, 1, v___x_2401_);
lean_ctor_set(v___x_2406_, 2, v___x_2405_);
v___y_2390_ = v___x_2406_;
goto v___jp_2389_;
}
else
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_unsigned_to_nat(0u);
v___x_2408_ = l_Lean_Syntax_getArg(v_term_2363_, v___x_2407_);
lean_dec(v_term_2363_);
v___y_2390_ = v___x_2408_;
goto v___jp_2389_;
}
}
else
{
v___y_2390_ = v_term_2363_;
goto v___jp_2389_;
}
v___jp_2372_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_inc(v___y_2375_);
v___x_2376_ = l_Lean_Name_append(v_kind_2362_, v___y_2375_);
v___x_2377_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2378_ = l_Lean_Name_append(v___x_2376_, v___x_2377_);
v___x_2379_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2380_ = lean_array_push(v___x_2379_, v_nesting_2371_);
v___x_2381_ = lean_array_push(v___x_2380_, v___y_2373_);
v___x_2382_ = lean_array_push(v___x_2381_, v___y_2374_);
v___x_2383_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2370_);
lean_ctor_set(v___x_2383_, 1, v___x_2378_);
lean_ctor_set(v___x_2383_, 2, v___x_2382_);
return v___x_2383_;
}
v___jp_2384_:
{
if (v_isPseudoKind_2366_ == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_box(0);
v___y_2373_ = v___y_2385_;
v___y_2374_ = v___y_2386_;
v___y_2375_ = v___x_2387_;
goto v___jp_2372_;
}
else
{
lean_object* v___x_2388_; 
v___x_2388_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2373_ = v___y_2385_;
v___y_2374_ = v___y_2386_;
v___y_2375_ = v___x_2388_;
goto v___jp_2372_;
}
}
v___jp_2389_:
{
if (lean_obj_tag(v_name_2365_) == 0)
{
lean_object* v___x_2391_; 
v___x_2391_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2385_ = v___y_2390_;
v___y_2386_ = v___x_2391_;
goto v___jp_2384_;
}
else
{
lean_object* v_val_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_val_2392_ = lean_ctor_get(v_name_2365_, 0);
lean_inc(v_val_2392_);
lean_dec_ref_known(v_name_2365_, 1);
v___x_2393_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2394_ = l_Lean_mkAtom(v_val_2392_);
v___x_2395_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2396_ = lean_array_push(v___x_2395_, v___x_2394_);
v___x_2397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2370_);
lean_ctor_set(v___x_2397_, 1, v___x_2393_);
lean_ctor_set(v___x_2397_, 2, v___x_2396_);
v___y_2385_ = v___y_2390_;
v___y_2386_ = v___x_2397_;
goto v___jp_2384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2409_, lean_object* v_term_2410_, lean_object* v_nesting_2411_, lean_object* v_name_2412_, lean_object* v_isPseudoKind_2413_){
_start:
{
uint8_t v_isPseudoKind_boxed_2414_; lean_object* v_res_2415_; 
v_isPseudoKind_boxed_2414_ = lean_unbox(v_isPseudoKind_2413_);
v_res_2415_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2409_, v_term_2410_, v_nesting_2411_, v_name_2412_, v_isPseudoKind_boxed_2414_);
return v_res_2415_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2416_){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_getArgs(v___x_2418_);
lean_dec(v___x_2418_);
v___x_2420_ = lean_array_get_size(v___x_2419_);
lean_dec_ref(v___x_2419_);
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_nat_dec_eq(v___x_2420_, v___x_2421_);
if (v___x_2422_ == 0)
{
uint8_t v___x_2423_; 
v___x_2423_ = 1;
return v___x_2423_;
}
else
{
uint8_t v___x_2424_; 
v___x_2424_ = 0;
return v___x_2424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2425_){
_start:
{
uint8_t v_res_2426_; lean_object* v_r_2427_; 
v_res_2426_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2425_);
lean_dec(v_stx_2425_);
v_r_2427_ = lean_box(v_res_2426_);
return v_r_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2428_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = l_Lean_Syntax_isAntiquot(v_stx_2428_);
if (v___x_2429_ == 0)
{
return v_stx_2428_;
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2430_ = lean_unsigned_to_nat(1u);
v___x_2431_ = l_Lean_Syntax_getArg(v_stx_2428_, v___x_2430_);
v___x_2432_ = l_Lean_Syntax_getArgs(v___x_2431_);
lean_dec(v___x_2431_);
v___x_2433_ = lean_array_pop(v___x_2432_);
v___x_2434_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2435_ = lean_box(2);
v___x_2436_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2434_);
lean_ctor_set(v___x_2436_, 2, v___x_2433_);
v___x_2437_ = l_Lean_Syntax_setArg(v_stx_2428_, v___x_2430_, v___x_2436_);
return v___x_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2438_){
_start:
{
lean_object* v___y_2440_; uint8_t v___x_2451_; 
v___x_2451_ = l_Lean_Syntax_isAntiquot(v_stx_2438_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_unsigned_to_nat(3u);
v___x_2453_ = l_Lean_Syntax_getArg(v_stx_2438_, v___x_2452_);
v___y_2440_ = v___x_2453_;
goto v___jp_2439_;
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_unsigned_to_nat(2u);
v___x_2455_ = l_Lean_Syntax_getArg(v_stx_2438_, v___x_2454_);
v___y_2440_ = v___x_2455_;
goto v___jp_2439_;
}
v___jp_2439_:
{
uint8_t v___x_2441_; 
v___x_2441_ = l_Lean_Syntax_isIdent(v___y_2440_);
if (v___x_2441_ == 0)
{
uint8_t v___x_2442_; 
v___x_2442_ = l_Lean_Syntax_isAtom(v___y_2440_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_unsigned_to_nat(1u);
v___x_2444_ = l_Lean_Syntax_getArg(v___y_2440_, v___x_2443_);
lean_dec(v___y_2440_);
return v___x_2444_;
}
else
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2445_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2446_ = lean_unsigned_to_nat(1u);
v___x_2447_ = lean_mk_empty_array_with_capacity(v___x_2446_);
v___x_2448_ = lean_array_push(v___x_2447_, v___y_2440_);
v___x_2449_ = lean_box(2);
v___x_2450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
lean_ctor_set(v___x_2450_, 1, v___x_2445_);
lean_ctor_set(v___x_2450_, 2, v___x_2448_);
return v___x_2450_;
}
}
else
{
return v___y_2440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2456_);
lean_dec(v_stx_2456_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2458_){
_start:
{
if (lean_obj_tag(v_x_2458_) == 1)
{
lean_object* v_kind_2459_; 
v_kind_2459_ = lean_ctor_get(v_x_2458_, 1);
if (lean_obj_tag(v_kind_2459_) == 1)
{
lean_object* v_pre_2460_; lean_object* v_str_2461_; 
v_pre_2460_ = lean_ctor_get(v_kind_2459_, 0);
v_str_2461_ = lean_ctor_get(v_kind_2459_, 1);
if (lean_obj_tag(v_pre_2460_) == 1)
{
lean_object* v_pre_2467_; lean_object* v_str_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_pre_2467_ = lean_ctor_get(v_pre_2460_, 0);
v_str_2468_ = lean_ctor_get(v_pre_2460_, 1);
v___x_2469_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2470_ = lean_string_dec_eq(v_str_2468_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2472_ = lean_string_dec_eq(v_str_2461_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_box(0);
return v___x_2473_;
}
else
{
goto v___jp_2462_;
}
}
else
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2475_ = lean_string_dec_eq(v_str_2461_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_box(0);
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_box(v___x_2475_);
lean_inc(v_pre_2467_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v_pre_2467_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2478_);
return v___x_2479_;
}
}
}
else
{
lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2480_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2481_ = lean_string_dec_eq(v_str_2461_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_box(0);
return v___x_2482_;
}
else
{
goto v___jp_2462_;
}
}
v___jp_2462_:
{
uint8_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2463_ = 0;
v___x_2464_ = lean_box(v___x_2463_);
lean_inc(v_pre_2460_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_pre_2460_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
return v___x_2466_;
}
}
else
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_box(0);
return v___x_2483_;
}
}
else
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_box(0);
return v___x_2484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2485_);
lean_dec(v_x_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2487_, size_t v_i_2488_, size_t v_stop_2489_, lean_object* v_b_2490_){
_start:
{
lean_object* v___y_2492_; uint8_t v___x_2496_; 
v___x_2496_ = lean_usize_dec_eq(v_i_2488_, v_stop_2489_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_array_uget_borrowed(v_as_2487_, v_i_2488_);
v___x_2498_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2497_);
if (lean_obj_tag(v___x_2498_) == 0)
{
v___y_2492_ = v_b_2490_;
goto v___jp_2491_;
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2500_; 
v_val_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_val_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = lean_array_push(v_b_2490_, v_val_2499_);
v___y_2492_ = v___x_2500_;
goto v___jp_2491_;
}
}
else
{
return v_b_2490_;
}
v___jp_2491_:
{
size_t v___x_2493_; size_t v___x_2494_; 
v___x_2493_ = ((size_t)1ULL);
v___x_2494_ = lean_usize_add(v_i_2488_, v___x_2493_);
v_i_2488_ = v___x_2494_;
v_b_2490_ = v___y_2492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2501_, lean_object* v_i_2502_, lean_object* v_stop_2503_, lean_object* v_b_2504_){
_start:
{
size_t v_i_boxed_2505_; size_t v_stop_boxed_2506_; lean_object* v_res_2507_; 
v_i_boxed_2505_ = lean_unbox_usize(v_i_2502_);
lean_dec(v_i_2502_);
v_stop_boxed_2506_ = lean_unbox_usize(v_stop_2503_);
lean_dec(v_stop_2503_);
v_res_2507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2501_, v_i_boxed_2505_, v_stop_boxed_2506_, v_b_2504_);
lean_dec_ref(v_as_2501_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2510_, lean_object* v_start_2511_, lean_object* v_stop_2512_){
_start:
{
lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2513_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2514_ = lean_nat_dec_lt(v_start_2511_, v_stop_2512_);
if (v___x_2514_ == 0)
{
return v___x_2513_;
}
else
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = lean_array_get_size(v_as_2510_);
v___x_2516_ = lean_nat_dec_le(v_stop_2512_, v___x_2515_);
if (v___x_2516_ == 0)
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_nat_dec_lt(v_start_2511_, v___x_2515_);
if (v___x_2517_ == 0)
{
return v___x_2513_;
}
else
{
size_t v___x_2518_; size_t v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = lean_usize_of_nat(v_start_2511_);
v___x_2519_ = lean_usize_of_nat(v___x_2515_);
v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2510_, v___x_2518_, v___x_2519_, v___x_2513_);
return v___x_2520_;
}
}
else
{
size_t v___x_2521_; size_t v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = lean_usize_of_nat(v_start_2511_);
v___x_2522_ = lean_usize_of_nat(v_stop_2512_);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2510_, v___x_2521_, v___x_2522_, v___x_2513_);
return v___x_2523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2524_, lean_object* v_start_2525_, lean_object* v_stop_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2524_, v_start_2525_, v_stop_2526_);
lean_dec(v_stop_2526_);
lean_dec(v_start_2525_);
lean_dec_ref(v_as_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2528_){
_start:
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2528_);
v___x_2530_ = l_Lean_Syntax_isOfKind(v_stx_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2528_);
lean_dec(v_stx_2528_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_box(0);
return v___x_2532_;
}
else
{
lean_object* v_val_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_val_2533_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2533_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2534_ = lean_box(0);
v___x_2535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2535_, 0, v_val_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
return v___x_2535_;
}
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2536_ = l_Lean_Syntax_getArgs(v_stx_2528_);
lean_dec(v_stx_2528_);
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = lean_array_get_size(v___x_2536_);
v___x_2539_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2536_, v___x_2537_, v___x_2538_);
lean_dec_ref(v___x_2536_);
v___x_2540_ = lean_array_to_list(v___x_2539_);
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2542_){
_start:
{
if (lean_obj_tag(v_x_2542_) == 1)
{
lean_object* v_kind_2543_; 
v_kind_2543_ = lean_ctor_get(v_x_2542_, 1);
if (lean_obj_tag(v_kind_2543_) == 1)
{
lean_object* v_pre_2544_; lean_object* v_str_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_pre_2544_ = lean_ctor_get(v_kind_2543_, 0);
v_str_2545_ = lean_ctor_get(v_kind_2543_, 1);
v___x_2546_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2547_ = lean_string_dec_eq(v_str_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
v___x_2548_ = lean_box(0);
return v___x_2548_;
}
else
{
lean_object* v___x_2549_; 
lean_inc(v_pre_2544_);
v___x_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_pre_2544_);
return v___x_2549_;
}
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_box(0);
return v___x_2550_;
}
}
else
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_box(0);
return v___x_2551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2552_);
lean_dec(v_x_2552_);
return v_res_2553_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2554_);
if (lean_obj_tag(v___x_2555_) == 0)
{
uint8_t v___x_2556_; 
v___x_2556_ = 0;
return v___x_2556_;
}
else
{
uint8_t v___x_2557_; 
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = 1;
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2558_){
_start:
{
uint8_t v_res_2559_; lean_object* v_r_2560_; 
v_res_2559_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2558_);
lean_dec(v_stx_2558_);
v_r_2560_ = lean_box(v_res_2559_);
return v_r_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2561_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = lean_unsigned_to_nat(3u);
v___x_2563_ = l_Lean_Syntax_getArg(v_stx_2561_, v___x_2562_);
v___x_2564_ = l_Lean_Syntax_getArgs(v___x_2563_);
lean_dec(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2565_);
lean_dec(v_stx_2565_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2567_){
_start:
{
uint8_t v___x_2568_; 
v___x_2568_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2567_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = l_Lean_Syntax_getArg(v_stx_2567_, v___x_2569_);
return v___x_2570_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_unsigned_to_nat(5u);
v___x_2572_ = l_Lean_Syntax_getArg(v_stx_2567_, v___x_2571_);
return v___x_2572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2573_);
lean_dec(v_stx_2573_);
return v_res_2574_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2580_ = l_Lean_mkAtom(v___x_2579_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2583_ = l_Lean_mkAtom(v___x_2582_);
return v___x_2583_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2584_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2585_ = lean_unsigned_to_nat(6u);
v___x_2586_ = lean_mk_empty_array_with_capacity(v___x_2585_);
v___x_2587_ = lean_array_push(v___x_2586_, v___x_2584_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2588_, lean_object* v_contents_2589_, lean_object* v_suffix_2590_, lean_object* v_nesting_2591_){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v_nesting_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2592_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2593_ = lean_mk_array(v_nesting_2591_, v___x_2592_);
v___x_2594_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2595_ = lean_box(2);
v_nesting_2596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2596_, 0, v___x_2595_);
lean_ctor_set(v_nesting_2596_, 1, v___x_2594_);
lean_ctor_set(v_nesting_2596_, 2, v___x_2593_);
v___x_2597_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2598_ = l_Lean_Name_append(v_kind_2588_, v___x_2597_);
v___x_2599_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2595_);
lean_ctor_set(v___x_2600_, 1, v___x_2594_);
lean_ctor_set(v___x_2600_, 2, v_contents_2589_);
v___x_2601_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2602_ = l_Lean_mkAtom(v_suffix_2590_);
v___x_2603_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2604_ = lean_array_push(v___x_2603_, v_nesting_2596_);
v___x_2605_ = lean_array_push(v___x_2604_, v___x_2599_);
v___x_2606_ = lean_array_push(v___x_2605_, v___x_2600_);
v___x_2607_ = lean_array_push(v___x_2606_, v___x_2601_);
v___x_2608_ = lean_array_push(v___x_2607_, v___x_2602_);
v___x_2609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2595_);
lean_ctor_set(v___x_2609_, 1, v___x_2598_);
lean_ctor_set(v___x_2609_, 2, v___x_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2611_){
_start:
{
if (lean_obj_tag(v_x_2611_) == 1)
{
lean_object* v_kind_2612_; 
v_kind_2612_ = lean_ctor_get(v_x_2611_, 1);
if (lean_obj_tag(v_kind_2612_) == 1)
{
lean_object* v_pre_2613_; lean_object* v_str_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_pre_2613_ = lean_ctor_get(v_kind_2612_, 0);
v_str_2614_ = lean_ctor_get(v_kind_2612_, 1);
v___x_2615_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2616_ = lean_string_dec_eq(v_str_2614_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_box(0);
return v___x_2617_;
}
else
{
lean_object* v___x_2618_; 
lean_inc(v_pre_2613_);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_pre_2613_);
return v___x_2618_;
}
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_box(0);
return v___x_2619_;
}
}
else
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_box(0);
return v___x_2620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2621_);
lean_dec(v_x_2621_);
return v_res_2622_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2623_);
if (lean_obj_tag(v___x_2624_) == 0)
{
uint8_t v___x_2625_; 
v___x_2625_ = 0;
return v___x_2625_;
}
else
{
uint8_t v___x_2626_; 
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = 1;
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2627_){
_start:
{
uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_res_2628_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2627_);
lean_dec(v_stx_2627_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2630_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = l_Lean_Syntax_getArg(v_stx_2630_, v___x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2633_);
lean_dec(v_stx_2633_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2637_, lean_object* v_inner_2638_, lean_object* v_suffix_2639_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2640_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2641_ = l_Lean_Name_append(v_kind_2637_, v___x_2640_);
v___x_2642_ = l_Lean_mkAtom(v_suffix_2639_);
v___x_2643_ = lean_unsigned_to_nat(2u);
v___x_2644_ = lean_mk_empty_array_with_capacity(v___x_2643_);
v___x_2645_ = lean_array_push(v___x_2644_, v_inner_2638_);
v___x_2646_ = lean_array_push(v___x_2645_, v___x_2642_);
v___x_2647_ = lean_box(2);
v___x_2648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
lean_ctor_set(v___x_2648_, 1, v___x_2641_);
lean_ctor_set(v___x_2648_, 2, v___x_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2652_){
_start:
{
lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2653_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2654_ = l_Lean_Syntax_isOfKind(v_stx_2652_, v___x_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2655_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2658_){
_start:
{
uint8_t v___y_2660_; uint8_t v___x_2663_; 
v___x_2663_ = l_Lean_Syntax_isAntiquot(v_stx_2658_);
if (v___x_2663_ == 0)
{
uint8_t v___x_2664_; 
v___x_2664_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2658_);
v___y_2660_ = v___x_2664_;
goto v___jp_2659_;
}
else
{
v___y_2660_ = v___x_2663_;
goto v___jp_2659_;
}
v___jp_2659_:
{
if (v___y_2660_ == 0)
{
uint8_t v___x_2661_; 
v___x_2661_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2658_);
if (v___x_2661_ == 0)
{
uint8_t v___x_2662_; 
v___x_2662_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2658_);
return v___x_2662_;
}
else
{
lean_dec(v_stx_2658_);
return v___x_2661_;
}
}
else
{
lean_dec(v_stx_2658_);
return v___y_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2665_){
_start:
{
uint8_t v_res_2666_; lean_object* v_r_2667_; 
v_res_2666_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2665_);
v_r_2667_ = lean_box(v_res_2666_);
return v_r_2667_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2671_, lean_object* v_stx_2672_, lean_object* v_visit_2673_, lean_object* v_stack_2674_, lean_object* v_accept_2675_, lean_object* v_a_2676_, lean_object* v_b_2677_){
_start:
{
lean_object* v_a_2679_; uint8_t v___x_2683_; 
v___x_2683_ = lean_nat_dec_lt(v_a_2676_, v_upperBound_2671_);
if (v___x_2683_ == 0)
{
lean_dec(v_a_2676_);
lean_dec_ref(v_accept_2675_);
lean_dec(v_stack_2674_);
lean_dec_ref(v_visit_2673_);
lean_dec(v_stx_2672_);
lean_inc_ref(v_b_2677_);
return v_b_2677_;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2684_ = lean_box(0);
v___x_2685_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2686_ = l_Lean_Syntax_getArg(v_stx_2672_, v_a_2676_);
lean_inc_ref(v_visit_2673_);
lean_inc(v___x_2686_);
v___x_2687_ = lean_apply_1(v_visit_2673_, v___x_2686_);
v___x_2688_ = lean_unbox(v___x_2687_);
if (v___x_2688_ == 0)
{
lean_dec(v___x_2686_);
v_a_2679_ = v___x_2685_;
goto v___jp_2678_;
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
lean_inc(v_a_2676_);
lean_inc(v_stx_2672_);
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v_stx_2672_);
lean_ctor_set(v___x_2689_, 1, v_a_2676_);
lean_inc(v_stack_2674_);
v___x_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v_stack_2674_);
lean_inc_ref(v_accept_2675_);
lean_inc_ref(v_visit_2673_);
v___x_2691_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2673_, v_accept_2675_, v___x_2690_, v___x_2686_);
if (lean_obj_tag(v___x_2691_) == 1)
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec(v_a_2676_);
lean_dec_ref(v_accept_2675_);
lean_dec(v_stack_2674_);
lean_dec_ref(v_visit_2673_);
lean_dec(v_stx_2672_);
v___x_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
lean_ctor_set(v___x_2693_, 1, v___x_2684_);
return v___x_2693_;
}
else
{
lean_dec(v___x_2691_);
v_a_2679_ = v___x_2685_;
goto v___jp_2678_;
}
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_nat_add(v_a_2676_, v___x_2680_);
lean_dec(v_a_2676_);
v_a_2676_ = v___x_2681_;
v_b_2677_ = v_a_2679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2694_, lean_object* v_accept_2695_, lean_object* v_stack_2696_, lean_object* v_stx_2697_){
_start:
{
lean_object* v___x_2698_; uint8_t v___x_2699_; 
lean_inc_ref(v_accept_2695_);
lean_inc(v_stx_2697_);
v___x_2698_ = lean_apply_1(v_accept_2695_, v_stx_2697_);
v___x_2699_ = lean_unbox(v___x_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v_fst_2705_; 
v___x_2700_ = l_Lean_Syntax_getNumArgs(v_stx_2697_);
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = lean_box(0);
v___x_2703_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2704_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2700_, v_stx_2697_, v_visit_2694_, v_stack_2696_, v_accept_2695_, v___x_2701_, v___x_2703_);
lean_dec(v___x_2700_);
v_fst_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_fst_2705_);
lean_dec_ref(v___x_2704_);
if (lean_obj_tag(v_fst_2705_) == 0)
{
return v___x_2702_;
}
else
{
lean_object* v_val_2706_; 
v_val_2706_ = lean_ctor_get(v_fst_2705_, 0);
lean_inc(v_val_2706_);
lean_dec_ref_known(v_fst_2705_, 1);
return v_val_2706_;
}
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec_ref(v_accept_2695_);
lean_dec_ref(v_visit_2694_);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_stx_2697_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v_stack_2696_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2711_, lean_object* v_stx_2712_, lean_object* v_visit_2713_, lean_object* v_stack_2714_, lean_object* v_accept_2715_, lean_object* v_a_2716_, lean_object* v_b_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2711_, v_stx_2712_, v_visit_2713_, v_stack_2714_, v_accept_2715_, v_a_2716_, v_b_2717_);
lean_dec_ref(v_b_2717_);
lean_dec(v_upperBound_2711_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2719_, lean_object* v_stx_2720_, lean_object* v_visit_2721_, lean_object* v_stack_2722_, lean_object* v_accept_2723_, lean_object* v_inst_2724_, lean_object* v_R_2725_, lean_object* v_a_2726_, lean_object* v_b_2727_, lean_object* v_c_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2719_, v_stx_2720_, v_visit_2721_, v_stack_2722_, v_accept_2723_, v_a_2726_, v_b_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2730_, lean_object* v_stx_2731_, lean_object* v_visit_2732_, lean_object* v_stack_2733_, lean_object* v_accept_2734_, lean_object* v_inst_2735_, lean_object* v_R_2736_, lean_object* v_a_2737_, lean_object* v_b_2738_, lean_object* v_c_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2730_, v_stx_2731_, v_visit_2732_, v_stack_2733_, v_accept_2734_, v_inst_2735_, v_R_2736_, v_a_2737_, v_b_2738_, v_c_2739_);
lean_dec_ref(v_b_2738_);
lean_dec(v_upperBound_2730_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2741_, lean_object* v_visit_2742_, lean_object* v_accept_2743_){
_start:
{
lean_object* v___x_2744_; uint8_t v___x_2745_; 
lean_inc_ref(v_visit_2742_);
lean_inc(v_root_2741_);
v___x_2744_ = lean_apply_1(v_visit_2742_, v_root_2741_);
v___x_2745_ = lean_unbox(v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
lean_dec_ref(v_accept_2743_);
lean_dec_ref(v_visit_2742_);
lean_dec(v_root_2741_);
v___x_2746_ = lean_box(0);
return v___x_2746_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2742_, v_accept_2743_, v___x_2747_, v_root_2741_);
return v___x_2748_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2749_, lean_object* v_x_2750_, lean_object* v_p_2751_){
_start:
{
if (lean_obj_tag(v_p_2751_) == 0)
{
lean_dec_ref(v_x_2750_);
return v___x_2749_;
}
else
{
lean_object* v_fst_2752_; lean_object* v_val_2753_; uint8_t v___x_2754_; 
v_fst_2752_ = lean_ctor_get(v_x_2750_, 0);
lean_inc(v_fst_2752_);
lean_dec_ref(v_x_2750_);
v_val_2753_ = lean_ctor_get(v_p_2751_, 0);
v___x_2754_ = l_Lean_Syntax_isOfKind(v_fst_2752_, v_val_2753_);
return v___x_2754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2755_, lean_object* v_x_2756_, lean_object* v_p_2757_){
_start:
{
uint8_t v___x_121__boxed_2758_; uint8_t v_res_2759_; lean_object* v_r_2760_; 
v___x_121__boxed_2758_ = lean_unbox(v___x_2755_);
v_res_2759_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_121__boxed_2758_, v_x_2756_, v_p_2757_);
lean_dec(v_p_2757_);
v_r_2760_ = lean_box(v_res_2759_);
return v_r_2760_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2761_){
_start:
{
if (lean_obj_tag(v_x_2761_) == 0)
{
uint8_t v___x_2762_; 
v___x_2762_ = 1;
return v___x_2762_;
}
else
{
lean_object* v_head_2763_; uint8_t v___x_2764_; 
v_head_2763_ = lean_ctor_get(v_x_2761_, 0);
v___x_2764_ = lean_unbox(v_head_2763_);
if (v___x_2764_ == 0)
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_unbox(v_head_2763_);
return v___x_2765_;
}
else
{
lean_object* v_tail_2766_; 
v_tail_2766_ = lean_ctor_get(v_x_2761_, 1);
v_x_2761_ = v_tail_2766_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2768_){
_start:
{
uint8_t v_res_2769_; lean_object* v_r_2770_; 
v_res_2769_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2768_);
lean_dec(v_x_2768_);
v_r_2770_ = lean_box(v_res_2769_);
return v_r_2770_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2773_, lean_object* v_pattern_2774_){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = l_List_lengthTR___redArg(v_pattern_2774_);
v___x_2776_ = l_List_lengthTR___redArg(v_stack_2773_);
v___x_2777_ = lean_nat_dec_le(v___x_2775_, v___x_2776_);
lean_dec(v___x_2776_);
lean_dec(v___x_2775_);
if (v___x_2777_ == 0)
{
lean_dec(v_pattern_2774_);
lean_dec(v_stack_2773_);
return v___x_2777_;
}
else
{
lean_object* v___x_2778_; lean_object* v___f_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2778_ = lean_box(v___x_2777_);
v___f_2779_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2779_, 0, v___x_2778_);
v___x_2780_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2781_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2779_, v_stack_2773_, v_pattern_2774_, v___x_2780_);
v___x_2782_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2781_);
lean_dec(v___x_2781_);
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2783_, lean_object* v_pattern_2784_){
_start:
{
uint8_t v_res_2785_; lean_object* v_r_2786_; 
v_res_2785_ = l_Lean_Syntax_Stack_matches(v_stack_2783_, v_pattern_2784_);
v_r_2786_ = lean_box(v_res_2785_);
return v_r_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2787_, lean_object* v_trailing_2788_){
_start:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2787_);
if (lean_obj_tag(v___x_2789_) == 1)
{
lean_object* v_val_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2825_; 
v_val_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2825_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_val_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2825_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
if (lean_obj_tag(v_val_2790_) == 0)
{
lean_object* v_trailing_2794_; lean_object* v_leading_2795_; lean_object* v_pos_2796_; lean_object* v_endPos_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2823_; 
v_trailing_2794_ = lean_ctor_get(v_val_2790_, 2);
v_leading_2795_ = lean_ctor_get(v_val_2790_, 0);
v_pos_2796_ = lean_ctor_get(v_val_2790_, 1);
v_endPos_2797_ = lean_ctor_get(v_val_2790_, 3);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_val_2790_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2799_ = v_val_2790_;
v_isShared_2800_ = v_isSharedCheck_2823_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_endPos_2797_);
lean_inc(v_trailing_2794_);
lean_inc(v_pos_2796_);
lean_inc(v_leading_2795_);
lean_dec(v_val_2790_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2823_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v_str_2801_; lean_object* v_startPos_2802_; lean_object* v_stopPos_2803_; lean_object* v_startPos_2804_; lean_object* v_stopPos_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2821_; 
v_str_2801_ = lean_ctor_get(v_trailing_2794_, 0);
lean_inc_ref(v_str_2801_);
v_startPos_2802_ = lean_ctor_get(v_trailing_2794_, 1);
lean_inc(v_startPos_2802_);
v_stopPos_2803_ = lean_ctor_get(v_trailing_2794_, 2);
lean_inc(v_stopPos_2803_);
lean_dec_ref(v_trailing_2794_);
v_startPos_2804_ = lean_ctor_get(v_trailing_2788_, 1);
v_stopPos_2805_ = lean_ctor_get(v_trailing_2788_, 2);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_trailing_2788_);
if (v_isSharedCheck_2821_ == 0)
{
lean_object* v_unused_2822_; 
v_unused_2822_ = lean_ctor_get(v_trailing_2788_, 0);
lean_dec(v_unused_2822_);
v___x_2807_ = v_trailing_2788_;
v_isShared_2808_ = v_isSharedCheck_2821_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_stopPos_2805_);
lean_inc(v_startPos_2804_);
lean_dec(v_trailing_2788_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2821_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_nat_dec_eq(v_stopPos_2803_, v_startPos_2804_);
lean_dec(v_startPos_2804_);
lean_dec(v_stopPos_2803_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_del_object(v___x_2807_);
lean_dec(v_stopPos_2805_);
lean_dec(v_startPos_2802_);
lean_dec_ref(v_str_2801_);
lean_del_object(v___x_2799_);
lean_dec(v_endPos_2797_);
lean_dec(v_pos_2796_);
lean_dec_ref(v_leading_2795_);
lean_del_object(v___x_2792_);
lean_dec(v_stx_2787_);
v___x_2810_ = lean_box(0);
return v___x_2810_;
}
else
{
lean_object* v_trailing_2812_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v_startPos_2802_);
lean_ctor_set(v___x_2807_, 0, v_str_2801_);
v_trailing_2812_ = v___x_2807_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_str_2801_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v_startPos_2802_);
lean_ctor_set(v_reuseFailAlloc_2820_, 2, v_stopPos_2805_);
v_trailing_2812_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2814_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 2, v_trailing_2812_);
v___x_2814_ = v___x_2799_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_leading_2795_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_pos_2796_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_trailing_2812_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_endPos_2797_);
v___x_2814_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = l_Lean_Syntax_setTailInfo(v_stx_2787_, v___x_2814_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2815_);
v___x_2817_ = v___x_2792_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2824_; 
lean_del_object(v___x_2792_);
lean_dec(v_val_2790_);
lean_dec_ref(v_trailing_2788_);
lean_dec(v_stx_2787_);
v___x_2824_ = lean_box(0);
return v___x_2824_;
}
}
}
else
{
lean_object* v___x_2826_; 
lean_dec(v___x_2789_);
lean_dec_ref(v_trailing_2788_);
lean_dec(v_stx_2787_);
v___x_2826_ = lean_box(0);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2827_, lean_object* v_trailing_2828_){
_start:
{
lean_object* v___x_2829_; 
lean_inc(v_stx_2827_);
v___x_2829_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2827_, v_trailing_2828_);
if (lean_obj_tag(v___x_2829_) == 0)
{
return v_stx_2827_;
}
else
{
lean_object* v_val_2830_; 
lean_dec(v_stx_2827_);
v_val_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_val_2830_);
lean_dec_ref_known(v___x_2829_, 1);
return v_val_2830_;
}
}
}
lean_object* runtime_initialize_Init_Data_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Lean_Data_Format(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* initialize_Init_Data_String_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif

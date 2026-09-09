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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_start_95_; lean_object* v_stop_96_; lean_object* v_start_97_; lean_object* v_stop_98_; uint8_t v_decide_99_; 
v_start_95_ = lean_ctor_get(v_x_93_, 0);
v_stop_96_ = lean_ctor_get(v_x_93_, 1);
v_start_97_ = lean_ctor_get(v_x_94_, 0);
v_stop_98_ = lean_ctor_get(v_x_94_, 1);
v_decide_99_ = lean_nat_dec_eq(v_start_95_, v_start_97_);
if (v_decide_99_ == 0)
{
return v_decide_99_;
}
else
{
uint8_t v_decide_100_; 
v_decide_100_ = lean_nat_dec_eq(v_stop_96_, v_stop_98_);
return v_decide_100_;
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
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_pos_121_, v___x_126_);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_stop_124_);
lean_dec(v___x_127_);
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_le(v_pos_121_, v_stop_124_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_contains___boxed(lean_object* v_r_130_, lean_object* v_pos_131_, lean_object* v_includeStop_132_){
_start:
{
uint8_t v_includeStop_boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_includeStop_boxed_133_ = lean_unbox(v_includeStop_132_);
v_res_134_ = l_Lean_Syntax_Range_contains(v_r_130_, v_pos_131_, v_includeStop_boxed_133_);
lean_dec(v_pos_131_);
lean_dec_ref(v_r_130_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_includes(lean_object* v_super_136_, lean_object* v_sub_137_, uint8_t v_includeSuperStop_138_, uint8_t v_includeSubStop_139_){
_start:
{
lean_object* v_start_140_; lean_object* v_stop_141_; lean_object* v_start_142_; lean_object* v_stop_143_; uint8_t v___y_145_; uint8_t v___x_151_; uint8_t v___y_153_; 
v_start_140_ = lean_ctor_get(v_super_136_, 0);
v_stop_141_ = lean_ctor_get(v_super_136_, 1);
v_start_142_ = lean_ctor_get(v_sub_137_, 0);
v_stop_143_ = lean_ctor_get(v_sub_137_, 1);
v___x_151_ = lean_nat_dec_le(v_start_140_, v_start_142_);
if (v___x_151_ == 0)
{
return v___x_151_;
}
else
{
if (v_includeSuperStop_138_ == 0)
{
v___y_153_ = v_includeSuperStop_138_;
goto v___jp_152_;
}
else
{
if (v_includeSubStop_139_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_stop_141_, v___x_154_);
v___x_156_ = lean_nat_dec_le(v_stop_143_, v___x_155_);
lean_dec(v___x_155_);
return v___x_156_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
v___y_153_ = v___x_157_;
goto v___jp_152_;
}
}
}
v___jp_144_:
{
if (v___y_145_ == 0)
{
uint8_t v___x_146_; 
v___x_146_ = lean_nat_dec_le(v_stop_143_, v_stop_141_);
return v___x_146_;
}
else
{
if (v_includeSubStop_139_ == 0)
{
uint8_t v___x_147_; 
v___x_147_ = lean_nat_dec_le(v_stop_143_, v_stop_141_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_nat_add(v_stop_143_, v___x_148_);
v___x_150_ = lean_nat_dec_le(v___x_149_, v_stop_141_);
lean_dec(v___x_149_);
return v___x_150_;
}
}
}
v___jp_152_:
{
if (v_includeSuperStop_138_ == 0)
{
v___y_145_ = v___x_151_;
goto v___jp_144_;
}
else
{
v___y_145_ = v___y_153_;
goto v___jp_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object* v_super_158_, lean_object* v_sub_159_, lean_object* v_includeSuperStop_160_, lean_object* v_includeSubStop_161_){
_start:
{
uint8_t v_includeSuperStop_boxed_162_; uint8_t v_includeSubStop_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_includeSuperStop_boxed_162_ = lean_unbox(v_includeSuperStop_160_);
v_includeSubStop_boxed_163_ = lean_unbox(v_includeSubStop_161_);
v_res_164_ = l_Lean_Syntax_Range_includes(v_super_158_, v_sub_159_, v_includeSuperStop_boxed_162_, v_includeSubStop_boxed_163_);
lean_dec_ref(v_sub_159_);
lean_dec_ref(v_super_158_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object* v_first_166_, lean_object* v_second_167_, uint8_t v_includeFirstStop_168_, uint8_t v_includeSecondStop_169_){
_start:
{
uint8_t v___y_171_; 
if (v_includeFirstStop_168_ == 0)
{
lean_object* v_start_180_; lean_object* v_stop_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_start_180_ = lean_ctor_get(v_second_167_, 0);
v_stop_181_ = lean_ctor_get(v_first_166_, 1);
v___x_182_ = lean_unsigned_to_nat(1u);
v___x_183_ = lean_nat_add(v_start_180_, v___x_182_);
v___x_184_ = lean_nat_dec_le(v___x_183_, v_stop_181_);
lean_dec(v___x_183_);
v___y_171_ = v___x_184_;
goto v___jp_170_;
}
else
{
lean_object* v_start_185_; lean_object* v_stop_186_; uint8_t v___x_187_; 
v_start_185_ = lean_ctor_get(v_second_167_, 0);
v_stop_186_ = lean_ctor_get(v_first_166_, 1);
v___x_187_ = lean_nat_dec_le(v_start_185_, v_stop_186_);
v___y_171_ = v___x_187_;
goto v___jp_170_;
}
v___jp_170_:
{
if (v___y_171_ == 0)
{
return v___y_171_;
}
else
{
if (v_includeSecondStop_169_ == 0)
{
lean_object* v_start_172_; lean_object* v_stop_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_start_172_ = lean_ctor_get(v_first_166_, 0);
v_stop_173_ = lean_ctor_get(v_second_167_, 1);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_start_172_, v___x_174_);
v___x_176_ = lean_nat_dec_le(v___x_175_, v_stop_173_);
lean_dec(v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_start_177_; lean_object* v_stop_178_; uint8_t v___x_179_; 
v_start_177_ = lean_ctor_get(v_first_166_, 0);
v_stop_178_ = lean_ctor_get(v_second_167_, 1);
v___x_179_ = lean_nat_dec_le(v_start_177_, v_stop_178_);
return v___x_179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object* v_first_188_, lean_object* v_second_189_, lean_object* v_includeFirstStop_190_, lean_object* v_includeSecondStop_191_){
_start:
{
uint8_t v_includeFirstStop_boxed_192_; uint8_t v_includeSecondStop_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_includeFirstStop_boxed_192_ = lean_unbox(v_includeFirstStop_190_);
v_includeSecondStop_boxed_193_ = lean_unbox(v_includeSecondStop_191_);
v_res_194_ = l_Lean_Syntax_Range_overlaps(v_first_188_, v_second_189_, v_includeFirstStop_boxed_192_, v_includeSecondStop_boxed_193_);
lean_dec_ref(v_second_189_);
lean_dec_ref(v_first_188_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object* v_r_196_){
_start:
{
lean_object* v_start_197_; lean_object* v_stop_198_; lean_object* v___x_199_; 
v_start_197_ = lean_ctor_get(v_r_196_, 0);
v_stop_198_ = lean_ctor_get(v_r_196_, 1);
v___x_199_ = lean_nat_sub(v_stop_198_, v_start_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object* v_r_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Syntax_Range_bsize(v_r_200_);
lean_dec_ref(v_r_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* v_trailing_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_203_) == 0)
{
lean_object* v_leading_204_; lean_object* v_pos_205_; lean_object* v_endPos_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_leading_204_ = lean_ctor_get(v_x_203_, 0);
v_pos_205_ = lean_ctor_get(v_x_203_, 1);
v_endPos_206_ = lean_ctor_get(v_x_203_, 3);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_203_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_x_203_, 2);
lean_dec(v_unused_214_);
v___x_208_ = v_x_203_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_endPos_206_);
lean_inc(v_pos_205_);
lean_inc(v_leading_204_);
lean_dec(v_x_203_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 2, v_trailing_202_);
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_leading_204_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_pos_205_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_trailing_202_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_endPos_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_dec_ref(v_trailing_202_);
return v_x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t v_canonicalOnly_215_, lean_object* v_info_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_SourceInfo_getPos_x3f(v_info_216_, v_canonicalOnly_215_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_val_219_; lean_object* v___x_220_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref_known(v___x_217_, 1);
v___x_220_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_216_, v_canonicalOnly_215_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
lean_dec(v_val_219_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_230_; 
v_val_222_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_230_ == 0)
{
v___x_224_ = v___x_220_;
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_val_222_);
lean_dec(v___x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_230_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_val_219_);
lean_ctor_set(v___x_226_, 1, v_val_222_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object* v_canonicalOnly_231_, lean_object* v_info_232_){
_start:
{
uint8_t v_canonicalOnly_boxed_233_; lean_object* v_res_234_; 
v_canonicalOnly_boxed_233_ = lean_unbox(v_canonicalOnly_231_);
v_res_234_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_233_, v_info_232_);
lean_dec(v_info_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t v_canonicalOnly_235_, lean_object* v_info_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_SourceInfo_getPos_x3f(v_info_236_, v_canonicalOnly_235_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v_val_239_; lean_object* v___x_240_; 
v_val_239_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v___x_237_, 1);
v___x_240_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_236_, v_canonicalOnly_235_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
lean_dec(v_val_239_);
v___x_241_ = lean_box(0);
return v___x_241_;
}
else
{
lean_object* v_val_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_250_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_250_ == 0)
{
v___x_244_ = v___x_240_;
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_val_242_);
lean_dec(v___x_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_250_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_val_239_);
lean_ctor_set(v___x_246_, 1, v_val_242_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_246_);
v___x_248_ = v___x_244_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object* v_canonicalOnly_251_, lean_object* v_info_252_){
_start:
{
uint8_t v_canonicalOnly_boxed_253_; lean_object* v_res_254_; 
v_canonicalOnly_boxed_253_ = lean_unbox(v_canonicalOnly_251_);
v_res_254_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_253_, v_info_252_);
lean_dec(v_info_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object* v_x_255_){
_start:
{
switch(lean_obj_tag(v_x_255_))
{
case 0:
{
lean_object* v_pos_256_; lean_object* v_endPos_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v_pos_256_ = lean_ctor_get(v_x_255_, 1);
lean_inc(v_pos_256_);
v_endPos_257_ = lean_ctor_get(v_x_255_, 3);
lean_inc(v_endPos_257_);
lean_dec_ref_known(v_x_255_, 4);
v___x_258_ = 0;
v___x_259_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_259_, 0, v_pos_256_);
lean_ctor_set(v___x_259_, 1, v_endPos_257_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*2, v___x_258_);
return v___x_259_;
}
case 1:
{
lean_object* v_pos_260_; lean_object* v_endPos_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_pos_260_ = lean_ctor_get(v_x_255_, 0);
v_endPos_261_ = lean_ctor_get(v_x_255_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_255_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v_x_255_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_endPos_261_);
lean_inc(v_pos_260_);
lean_dec(v_x_255_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
uint8_t v___x_265_; lean_object* v___x_267_; 
v___x_265_ = 0;
if (v_isShared_264_ == 0)
{
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_pos_260_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_endPos_261_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_ctor_set_uint8(v___x_267_, sizeof(void*)*2, v___x_265_);
return v___x_267_;
}
}
}
default: 
{
return v_x_255_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
switch(lean_obj_tag(v_x_270_))
{
case 0:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v_leading_272_; lean_object* v_pos_273_; lean_object* v_trailing_274_; lean_object* v_endPos_275_; lean_object* v_leading_276_; lean_object* v_pos_277_; lean_object* v_trailing_278_; lean_object* v_endPos_279_; uint8_t v___x_280_; 
v_leading_272_ = lean_ctor_get(v_x_270_, 0);
lean_inc_ref(v_leading_272_);
v_pos_273_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_pos_273_);
v_trailing_274_ = lean_ctor_get(v_x_270_, 2);
lean_inc_ref(v_trailing_274_);
v_endPos_275_ = lean_ctor_get(v_x_270_, 3);
lean_inc(v_endPos_275_);
lean_dec_ref_known(v_x_270_, 4);
v_leading_276_ = lean_ctor_get(v_x_271_, 0);
lean_inc_ref(v_leading_276_);
v_pos_277_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_pos_277_);
v_trailing_278_ = lean_ctor_get(v_x_271_, 2);
lean_inc_ref(v_trailing_278_);
v_endPos_279_ = lean_ctor_get(v_x_271_, 3);
lean_inc(v_endPos_279_);
lean_dec_ref_known(v_x_271_, 4);
v___x_280_ = l_Substring_Raw_beq(v_leading_272_, v_leading_276_);
if (v___x_280_ == 0)
{
lean_dec(v_endPos_279_);
lean_dec_ref(v_trailing_278_);
lean_dec(v_pos_277_);
lean_dec(v_endPos_275_);
lean_dec_ref(v_trailing_274_);
lean_dec(v_pos_273_);
return v___x_280_;
}
else
{
uint8_t v_decide_281_; 
v_decide_281_ = lean_nat_dec_eq(v_pos_273_, v_pos_277_);
lean_dec(v_pos_277_);
lean_dec(v_pos_273_);
if (v_decide_281_ == 0)
{
lean_dec(v_endPos_279_);
lean_dec_ref(v_trailing_278_);
lean_dec(v_endPos_275_);
lean_dec_ref(v_trailing_274_);
return v_decide_281_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = l_Substring_Raw_beq(v_trailing_274_, v_trailing_278_);
if (v___x_282_ == 0)
{
lean_dec(v_endPos_279_);
lean_dec(v_endPos_275_);
return v___x_282_;
}
else
{
uint8_t v_decide_283_; 
v_decide_283_ = lean_nat_dec_eq(v_endPos_275_, v_endPos_279_);
lean_dec(v_endPos_279_);
lean_dec(v_endPos_275_);
return v_decide_283_;
}
}
}
}
else
{
uint8_t v___x_284_; 
lean_dec_ref_known(v_x_270_, 4);
lean_dec(v_x_271_);
v___x_284_ = 0;
return v___x_284_;
}
}
case 1:
{
if (lean_obj_tag(v_x_271_) == 1)
{
lean_object* v_pos_285_; lean_object* v_endPos_286_; uint8_t v_canonical_287_; lean_object* v_pos_288_; lean_object* v_endPos_289_; uint8_t v_canonical_290_; uint8_t v_decide_291_; 
v_pos_285_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_pos_285_);
v_endPos_286_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_endPos_286_);
v_canonical_287_ = lean_ctor_get_uint8(v_x_270_, sizeof(void*)*2);
lean_dec_ref_known(v_x_270_, 2);
v_pos_288_ = lean_ctor_get(v_x_271_, 0);
lean_inc(v_pos_288_);
v_endPos_289_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_endPos_289_);
v_canonical_290_ = lean_ctor_get_uint8(v_x_271_, sizeof(void*)*2);
lean_dec_ref_known(v_x_271_, 2);
v_decide_291_ = lean_nat_dec_eq(v_pos_285_, v_pos_288_);
lean_dec(v_pos_288_);
lean_dec(v_pos_285_);
if (v_decide_291_ == 0)
{
lean_dec(v_endPos_289_);
lean_dec(v_endPos_286_);
return v_decide_291_;
}
else
{
uint8_t v_decide_292_; 
v_decide_292_ = lean_nat_dec_eq(v_endPos_286_, v_endPos_289_);
lean_dec(v_endPos_289_);
lean_dec(v_endPos_286_);
if (v_decide_292_ == 0)
{
return v_decide_292_;
}
else
{
if (v_canonical_290_ == 0)
{
if (v_canonical_287_ == 0)
{
return v_decide_292_;
}
else
{
return v_canonical_290_;
}
}
else
{
return v_canonical_287_;
}
}
}
}
else
{
uint8_t v___x_293_; 
lean_dec_ref_known(v_x_270_, 2);
lean_dec(v_x_271_);
v___x_293_ = 0;
return v___x_293_;
}
}
default: 
{
if (lean_obj_tag(v_x_271_) == 2)
{
uint8_t v___x_294_; 
v___x_294_ = 1;
return v___x_294_;
}
else
{
uint8_t v___x_295_; 
lean_dec(v_x_271_);
v___x_295_ = 0;
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
uint8_t v_res_298_; lean_object* v_r_299_; 
v_res_298_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_296_, v_x_297_);
v_r_299_ = lean_box(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object* v_00_u03b2_302_, lean_object* v_a_303_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object* v_00_u03b2_304_, lean_object* v_info_305_, lean_object* v_val_306_, lean_object* v_a_307_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* v_00_u03b2_308_, lean_object* v_info_309_, lean_object* v_val_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_308_, v_info_309_, v_val_310_, v_a_311_);
lean_dec_ref(v_val_310_);
lean_dec(v_info_309_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object* v_00_u03b2_313_, lean_object* v_info_314_, lean_object* v_rawVal_315_, lean_object* v_val_316_, lean_object* v_preresolved_317_, lean_object* v_a_318_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* v_00_u03b2_319_, lean_object* v_info_320_, lean_object* v_rawVal_321_, lean_object* v_val_322_, lean_object* v_preresolved_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_unreachIsNodeIdent(v_00_u03b2_319_, v_info_320_, v_rawVal_321_, v_val_322_, v_preresolved_323_, v_a_324_);
lean_dec(v_preresolved_323_);
lean_dec(v_val_322_);
lean_dec_ref(v_rawVal_321_);
lean_dec(v_info_320_);
return v_res_325_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object* v_k_341_){
_start:
{
uint8_t v___y_343_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_isLitKind___closed__7));
v___x_351_ = lean_name_eq(v_k_341_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_isLitKind___closed__9));
v___x_353_ = lean_name_eq(v_k_341_, v___x_352_);
v___y_343_ = v___x_353_;
goto v___jp_342_;
}
else
{
v___y_343_ = v___x_351_;
goto v___jp_342_;
}
v___jp_342_:
{
if (v___y_343_ == 0)
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = ((lean_object*)(l_Lean_isLitKind___closed__1));
v___x_345_ = lean_name_eq(v_k_341_, v___x_344_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = ((lean_object*)(l_Lean_isLitKind___closed__3));
v___x_347_ = lean_name_eq(v_k_341_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_isLitKind___closed__5));
v___x_349_ = lean_name_eq(v_k_341_, v___x_348_);
return v___x_349_;
}
else
{
return v___x_347_;
}
}
else
{
return v___x_345_;
}
}
else
{
return v___y_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object* v_k_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_isLitKind(v_k_354_);
lean_dec(v_k_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object* v_n_357_){
_start:
{
lean_object* v_kind_358_; 
v_kind_358_ = lean_ctor_get(v_n_357_, 1);
lean_inc(v_kind_358_);
return v_kind_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* v_n_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_SyntaxNode_getKind(v_n_359_);
lean_dec(v_n_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object* v_n_361_, lean_object* v_fn_362_){
_start:
{
lean_object* v_args_363_; lean_object* v___x_364_; 
v_args_363_ = lean_ctor_get(v_n_361_, 2);
lean_inc_ref(v_args_363_);
lean_dec(v_n_361_);
v___x_364_ = lean_apply_1(v_fn_362_, v_args_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object* v_00_u03b2_365_, lean_object* v_n_366_, lean_object* v_fn_367_){
_start:
{
lean_object* v_args_368_; lean_object* v___x_369_; 
v_args_368_ = lean_ctor_get(v_n_366_, 2);
lean_inc_ref(v_args_368_);
lean_dec(v_n_366_);
v___x_369_ = lean_apply_1(v_fn_367_, v_args_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* v_n_370_){
_start:
{
lean_object* v_args_371_; lean_object* v___x_372_; 
v_args_371_ = lean_ctor_get(v_n_370_, 2);
v___x_372_ = lean_array_get_size(v_args_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* v_n_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_SyntaxNode_getNumArgs(v_n_373_);
lean_dec(v_n_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object* v_n_375_, lean_object* v_i_376_){
_start:
{
lean_object* v_args_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_args_377_ = lean_ctor_get(v_n_375_, 2);
v___x_378_ = lean_box(0);
v___x_379_ = lean_array_get_borrowed(v___x_378_, v_args_377_, v_i_376_);
lean_inc(v___x_379_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* v_n_380_, lean_object* v_i_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_SyntaxNode_getArg(v_n_380_, v_i_381_);
lean_dec(v_i_381_);
lean_dec(v_n_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object* v_n_383_){
_start:
{
lean_object* v_args_384_; 
v_args_384_ = lean_ctor_get(v_n_383_, 2);
lean_inc_ref(v_args_384_);
return v_args_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* v_n_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_SyntaxNode_getArgs(v_n_385_);
lean_dec(v_n_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* v_n_387_, lean_object* v_fn_388_){
_start:
{
lean_object* v_info_389_; lean_object* v_kind_390_; lean_object* v_args_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_399_; 
v_info_389_ = lean_ctor_get(v_n_387_, 0);
v_kind_390_ = lean_ctor_get(v_n_387_, 1);
v_args_391_ = lean_ctor_get(v_n_387_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v_n_387_);
if (v_isSharedCheck_399_ == 0)
{
v___x_393_ = v_n_387_;
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_args_391_);
lean_inc(v_kind_390_);
lean_inc(v_info_389_);
lean_dec(v_n_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_395_ = lean_apply_1(v_fn_388_, v_args_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 2, v___x_395_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_info_389_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_kind_390_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
if (lean_obj_tag(v_x_401_) == 0)
{
uint8_t v___x_402_; 
v___x_402_ = 1;
return v___x_402_;
}
else
{
uint8_t v___x_403_; 
v___x_403_ = 0;
return v___x_403_;
}
}
else
{
if (lean_obj_tag(v_x_401_) == 0)
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
else
{
lean_object* v_val_405_; lean_object* v_val_406_; uint8_t v___x_407_; 
v_val_405_ = lean_ctor_get(v_x_400_, 0);
v_val_406_ = lean_ctor_get(v_x_401_, 0);
v___x_407_ = l_Lean_Syntax_instBEqRange_beq(v_val_405_, v_val_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v_x_408_, v_x_409_);
lean_dec(v_x_409_);
lean_dec(v_x_408_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
if (lean_obj_tag(v_x_413_) == 0)
{
uint8_t v___x_414_; 
v___x_414_ = 1;
return v___x_414_;
}
else
{
uint8_t v___x_415_; 
v___x_415_ = 0;
return v___x_415_;
}
}
else
{
if (lean_obj_tag(v_x_413_) == 0)
{
uint8_t v___x_416_; 
v___x_416_ = 0;
return v___x_416_;
}
else
{
lean_object* v_head_417_; lean_object* v_tail_418_; lean_object* v_head_419_; lean_object* v_tail_420_; uint8_t v___x_421_; 
v_head_417_ = lean_ctor_get(v_x_412_, 0);
v_tail_418_ = lean_ctor_get(v_x_412_, 1);
v_head_419_ = lean_ctor_get(v_x_413_, 0);
v_tail_420_ = lean_ctor_get(v_x_413_, 1);
v___x_421_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_417_, v_head_419_);
if (v___x_421_ == 0)
{
return v___x_421_;
}
else
{
v_x_412_ = v_tail_418_;
v_x_413_ = v_tail_420_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
uint8_t v_res_425_; lean_object* v_r_426_; 
v_res_425_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_423_, v_x_424_);
lean_dec(v_x_424_);
lean_dec(v_x_423_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
switch(lean_obj_tag(v_x_427_))
{
case 0:
{
if (lean_obj_tag(v_x_428_) == 0)
{
uint8_t v___x_429_; 
v___x_429_ = 1;
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
lean_dec(v_x_428_);
v___x_430_ = 0;
return v___x_430_;
}
}
case 1:
{
if (lean_obj_tag(v_x_428_) == 1)
{
lean_object* v_info_431_; lean_object* v_kind_432_; lean_object* v_args_433_; lean_object* v_info_434_; lean_object* v_kind_435_; lean_object* v_args_436_; uint8_t v___y_438_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_info_431_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_info_431_);
v_kind_432_ = lean_ctor_get(v_x_427_, 1);
lean_inc(v_kind_432_);
v_args_433_ = lean_ctor_get(v_x_427_, 2);
lean_inc_ref(v_args_433_);
lean_dec_ref_known(v_x_427_, 3);
v_info_434_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_info_434_);
v_kind_435_ = lean_ctor_get(v_x_428_, 1);
lean_inc(v_kind_435_);
v_args_436_ = lean_ctor_get(v_x_428_, 2);
lean_inc_ref(v_args_436_);
lean_dec_ref_known(v_x_428_, 3);
v___x_443_ = 0;
v___x_444_ = l_Lean_SourceInfo_getRange_x3f(v___x_443_, v_info_431_);
lean_dec(v_info_431_);
v___x_445_ = l_Lean_SourceInfo_getRange_x3f(v___x_443_, v_info_434_);
lean_dec(v_info_434_);
v___x_446_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_444_, v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_444_);
if (v___x_446_ == 0)
{
lean_dec(v_kind_435_);
lean_dec(v_kind_432_);
v___y_438_ = v___x_446_;
goto v___jp_437_;
}
else
{
uint8_t v___x_447_; 
v___x_447_ = lean_name_eq(v_kind_432_, v_kind_435_);
lean_dec(v_kind_435_);
lean_dec(v_kind_432_);
v___y_438_ = v___x_447_;
goto v___jp_437_;
}
v___jp_437_:
{
if (v___y_438_ == 0)
{
lean_dec_ref(v_args_436_);
lean_dec_ref(v_args_433_);
return v___y_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_439_ = lean_array_get_size(v_args_433_);
v___x_440_ = lean_array_get_size(v_args_436_);
v___x_441_ = lean_nat_dec_eq(v___x_439_, v___x_440_);
if (v___x_441_ == 0)
{
lean_dec_ref(v_args_436_);
lean_dec_ref(v_args_433_);
return v___x_441_;
}
else
{
uint8_t v___x_442_; 
v___x_442_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_args_433_, v_args_436_, v___x_439_);
lean_dec_ref(v_args_436_);
lean_dec_ref(v_args_433_);
return v___x_442_;
}
}
}
}
else
{
uint8_t v___x_448_; 
lean_dec_ref_known(v_x_427_, 3);
lean_dec(v_x_428_);
v___x_448_ = 0;
return v___x_448_;
}
}
case 2:
{
if (lean_obj_tag(v_x_428_) == 2)
{
lean_object* v_info_449_; lean_object* v_val_450_; lean_object* v_info_451_; lean_object* v_val_452_; uint8_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_info_449_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_info_449_);
v_val_450_ = lean_ctor_get(v_x_427_, 1);
lean_inc_ref(v_val_450_);
lean_dec_ref_known(v_x_427_, 2);
v_info_451_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_info_451_);
v_val_452_ = lean_ctor_get(v_x_428_, 1);
lean_inc_ref(v_val_452_);
lean_dec_ref_known(v_x_428_, 2);
v___x_453_ = 0;
v___x_454_ = l_Lean_SourceInfo_getRange_x3f(v___x_453_, v_info_449_);
lean_dec(v_info_449_);
v___x_455_ = l_Lean_SourceInfo_getRange_x3f(v___x_453_, v_info_451_);
lean_dec(v_info_451_);
v___x_456_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_454_, v___x_455_);
lean_dec(v___x_455_);
lean_dec(v___x_454_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_val_452_);
lean_dec_ref(v_val_450_);
return v___x_456_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = lean_string_dec_eq(v_val_450_, v_val_452_);
lean_dec_ref(v_val_452_);
lean_dec_ref(v_val_450_);
return v___x_457_;
}
}
else
{
uint8_t v___x_458_; 
lean_dec_ref_known(v_x_427_, 2);
lean_dec(v_x_428_);
v___x_458_ = 0;
return v___x_458_;
}
}
default: 
{
if (lean_obj_tag(v_x_428_) == 3)
{
lean_object* v_info_459_; lean_object* v_rawVal_460_; lean_object* v_val_461_; lean_object* v_preresolved_462_; lean_object* v_info_463_; lean_object* v_rawVal_464_; lean_object* v_val_465_; lean_object* v_preresolved_466_; uint8_t v___y_468_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_info_459_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_info_459_);
v_rawVal_460_ = lean_ctor_get(v_x_427_, 1);
lean_inc_ref(v_rawVal_460_);
v_val_461_ = lean_ctor_get(v_x_427_, 2);
lean_inc(v_val_461_);
v_preresolved_462_ = lean_ctor_get(v_x_427_, 3);
lean_inc(v_preresolved_462_);
lean_dec_ref_known(v_x_427_, 4);
v_info_463_ = lean_ctor_get(v_x_428_, 0);
lean_inc(v_info_463_);
v_rawVal_464_ = lean_ctor_get(v_x_428_, 1);
lean_inc_ref(v_rawVal_464_);
v_val_465_ = lean_ctor_get(v_x_428_, 2);
lean_inc(v_val_465_);
v_preresolved_466_ = lean_ctor_get(v_x_428_, 3);
lean_inc(v_preresolved_466_);
lean_dec_ref_known(v_x_428_, 4);
v___x_471_ = 0;
v___x_472_ = l_Lean_SourceInfo_getRange_x3f(v___x_471_, v_info_459_);
lean_dec(v_info_459_);
v___x_473_ = l_Lean_SourceInfo_getRange_x3f(v___x_471_, v_info_463_);
lean_dec(v_info_463_);
v___x_474_ = l_Option_instBEq_beq___at___00Lean_Syntax_structRangeEq_spec__1(v___x_472_, v___x_473_);
lean_dec(v___x_473_);
lean_dec(v___x_472_);
if (v___x_474_ == 0)
{
lean_dec_ref(v_rawVal_464_);
lean_dec_ref(v_rawVal_460_);
v___y_468_ = v___x_474_;
goto v___jp_467_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = l_Substring_Raw_beq(v_rawVal_460_, v_rawVal_464_);
v___y_468_ = v___x_475_;
goto v___jp_467_;
}
v___jp_467_:
{
if (v___y_468_ == 0)
{
lean_dec(v_preresolved_466_);
lean_dec(v_val_465_);
lean_dec(v_preresolved_462_);
lean_dec(v_val_461_);
return v___y_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = lean_name_eq(v_val_461_, v_val_465_);
lean_dec(v_val_465_);
lean_dec(v_val_461_);
if (v___x_469_ == 0)
{
lean_dec(v_preresolved_466_);
lean_dec(v_preresolved_462_);
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_462_, v_preresolved_466_);
lean_dec(v_preresolved_466_);
lean_dec(v_preresolved_462_);
return v___x_470_;
}
}
}
}
else
{
uint8_t v___x_476_; 
lean_dec_ref_known(v_x_427_, 4);
lean_dec(v_x_428_);
v___x_476_ = 0;
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(lean_object* v_xs_477_, lean_object* v_ys_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_zero_480_; uint8_t v_isZero_481_; 
v_zero_480_ = lean_unsigned_to_nat(0u);
v_isZero_481_ = lean_nat_dec_eq(v_x_479_, v_zero_480_);
if (v_isZero_481_ == 1)
{
lean_dec(v_x_479_);
return v_isZero_481_;
}
else
{
lean_object* v_one_482_; lean_object* v_n_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_one_482_ = lean_unsigned_to_nat(1u);
v_n_483_ = lean_nat_sub(v_x_479_, v_one_482_);
lean_dec(v_x_479_);
v___x_484_ = lean_array_fget_borrowed(v_xs_477_, v_n_483_);
v___x_485_ = lean_array_fget_borrowed(v_ys_478_, v_n_483_);
lean_inc(v___x_485_);
lean_inc(v___x_484_);
v___x_486_ = l_Lean_Syntax_structRangeEq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec(v_n_483_);
return v___x_486_;
}
else
{
v_x_479_ = v_n_483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg___boxed(lean_object* v_xs_488_, lean_object* v_ys_489_, lean_object* v_x_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_488_, v_ys_489_, v_x_490_);
lean_dec_ref(v_ys_489_);
lean_dec_ref(v_xs_488_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Lean_Syntax_structRangeEq(v_x_493_, v_x_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(lean_object* v_xs_497_, lean_object* v_ys_498_, lean_object* v_hsz_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
uint8_t v___x_502_; 
v___x_502_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___redArg(v_xs_497_, v_ys_498_, v_x_500_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object* v_xs_503_, lean_object* v_ys_504_, lean_object* v_hsz_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__0(v_xs_503_, v_ys_504_, v_hsz_505_, v_x_506_, v_x_507_);
lean_dec_ref(v_ys_504_);
lean_dec_ref(v_xs_503_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t v___x_510_, lean_object* v_x_511_){
_start:
{
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object* v___x_512_, lean_object* v_x_513_){
_start:
{
uint8_t v___x_92__boxed_514_; uint8_t v_res_515_; lean_object* v_r_516_; 
v___x_92__boxed_514_ = lean_unbox(v___x_512_);
v_res_515_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_92__boxed_514_, v_x_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object* v_opts_526_, lean_object* v_stx1_527_, lean_object* v_stx2_528_){
_start:
{
uint8_t v___x_529_; uint8_t v___x_530_; 
lean_inc(v_stx2_528_);
lean_inc(v_stx1_527_);
v___x_529_ = l_Lean_Syntax_structRangeEq(v_stx1_527_, v_stx2_528_);
v___x_530_ = 1;
if (v___x_529_ == 0)
{
lean_object* v_map_531_; lean_object* v___x_532_; lean_object* v___f_533_; uint8_t v___y_535_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_map_531_ = lean_ctor_get(v_opts_526_, 0);
v___x_532_ = lean_box(v___x_529_);
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_533_, 0, v___x_532_);
v___x_550_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_551_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_531_, v___x_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
v___y_535_ = v___x_529_;
goto v___jp_534_;
}
else
{
lean_object* v_val_552_; 
v_val_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_552_);
lean_dec_ref_known(v___x_551_, 1);
if (lean_obj_tag(v_val_552_) == 1)
{
uint8_t v_v_553_; 
v_v_553_ = lean_ctor_get_uint8(v_val_552_, 0);
lean_dec_ref_known(v_val_552_, 0);
v___y_535_ = v_v_553_;
goto v___jp_534_;
}
else
{
lean_dec(v_val_552_);
v___y_535_ = v___x_529_;
goto v___jp_534_;
}
}
v___jp_534_:
{
if (v___y_535_ == 0)
{
lean_dec_ref(v___f_533_);
lean_dec(v_stx2_528_);
lean_dec(v_stx1_527_);
return v___x_529_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_536_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_537_ = lean_box(0);
v___x_538_ = l_Lean_Syntax_formatStx(v_stx1_527_, v___x_537_, v___x_530_);
v___x_539_ = l_Std_Format_defWidth;
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = l_Std_Format_pretty(v___x_538_, v___x_539_, v___x_540_, v___x_540_);
v___x_542_ = lean_string_append(v___x_536_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_544_ = lean_string_append(v___x_542_, v___x_543_);
v___x_545_ = l_Lean_Syntax_formatStx(v_stx2_528_, v___x_537_, v___x_530_);
v___x_546_ = l_Std_Format_pretty(v___x_545_, v___x_539_, v___x_540_, v___x_540_);
v___x_547_ = lean_string_append(v___x_544_, v___x_546_);
lean_dec_ref(v___x_546_);
v___x_548_ = lean_dbg_trace(v___x_547_, v___f_533_);
v___x_549_ = lean_unbox(v___x_548_);
lean_dec(v___x_548_);
return v___x_549_;
}
}
}
else
{
lean_dec(v_stx2_528_);
lean_dec(v_stx1_527_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object* v_opts_554_, lean_object* v_stx1_555_, lean_object* v_stx2_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_554_, v_stx1_555_, v_stx2_556_);
lean_dec_ref(v_opts_554_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
switch(lean_obj_tag(v_x_559_))
{
case 0:
{
if (lean_obj_tag(v_x_560_) == 0)
{
uint8_t v___x_561_; 
v___x_561_ = 1;
return v___x_561_;
}
else
{
uint8_t v___x_562_; 
lean_dec(v_x_560_);
v___x_562_ = 0;
return v___x_562_;
}
}
case 1:
{
if (lean_obj_tag(v_x_560_) == 1)
{
lean_object* v_info_563_; lean_object* v_kind_564_; lean_object* v_args_565_; lean_object* v_info_566_; lean_object* v_kind_567_; lean_object* v_args_568_; uint8_t v___y_570_; uint8_t v___x_575_; 
v_info_563_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_info_563_);
v_kind_564_ = lean_ctor_get(v_x_559_, 1);
lean_inc(v_kind_564_);
v_args_565_ = lean_ctor_get(v_x_559_, 2);
lean_inc_ref(v_args_565_);
lean_dec_ref_known(v_x_559_, 3);
v_info_566_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_info_566_);
v_kind_567_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_kind_567_);
v_args_568_ = lean_ctor_get(v_x_560_, 2);
lean_inc_ref(v_args_568_);
lean_dec_ref_known(v_x_560_, 3);
v___x_575_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_563_, v_info_566_);
if (v___x_575_ == 0)
{
lean_dec(v_kind_567_);
lean_dec(v_kind_564_);
v___y_570_ = v___x_575_;
goto v___jp_569_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = lean_name_eq(v_kind_564_, v_kind_567_);
lean_dec(v_kind_567_);
lean_dec(v_kind_564_);
v___y_570_ = v___x_576_;
goto v___jp_569_;
}
v___jp_569_:
{
if (v___y_570_ == 0)
{
lean_dec_ref(v_args_568_);
lean_dec_ref(v_args_565_);
return v___y_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_array_get_size(v_args_565_);
v___x_572_ = lean_array_get_size(v_args_568_);
v___x_573_ = lean_nat_dec_eq(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec_ref(v_args_568_);
lean_dec_ref(v_args_565_);
return v___x_573_;
}
else
{
uint8_t v___x_574_; 
v___x_574_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_args_565_, v_args_568_, v___x_571_);
lean_dec_ref(v_args_568_);
lean_dec_ref(v_args_565_);
return v___x_574_;
}
}
}
}
else
{
uint8_t v___x_577_; 
lean_dec_ref_known(v_x_559_, 3);
lean_dec(v_x_560_);
v___x_577_ = 0;
return v___x_577_;
}
}
case 2:
{
if (lean_obj_tag(v_x_560_) == 2)
{
lean_object* v_info_578_; lean_object* v_val_579_; lean_object* v_info_580_; lean_object* v_val_581_; uint8_t v___x_582_; 
v_info_578_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_info_578_);
v_val_579_ = lean_ctor_get(v_x_559_, 1);
lean_inc_ref(v_val_579_);
lean_dec_ref_known(v_x_559_, 2);
v_info_580_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_info_580_);
v_val_581_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_val_581_);
lean_dec_ref_known(v_x_560_, 2);
v___x_582_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_578_, v_info_580_);
if (v___x_582_ == 0)
{
lean_dec_ref(v_val_581_);
lean_dec_ref(v_val_579_);
return v___x_582_;
}
else
{
uint8_t v___x_583_; 
v___x_583_ = lean_string_dec_eq(v_val_579_, v_val_581_);
lean_dec_ref(v_val_581_);
lean_dec_ref(v_val_579_);
return v___x_583_;
}
}
else
{
uint8_t v___x_584_; 
lean_dec_ref_known(v_x_559_, 2);
lean_dec(v_x_560_);
v___x_584_ = 0;
return v___x_584_;
}
}
default: 
{
if (lean_obj_tag(v_x_560_) == 3)
{
lean_object* v_info_585_; lean_object* v_rawVal_586_; lean_object* v_val_587_; lean_object* v_preresolved_588_; lean_object* v_info_589_; lean_object* v_rawVal_590_; lean_object* v_val_591_; lean_object* v_preresolved_592_; uint8_t v___y_594_; uint8_t v___x_597_; 
v_info_585_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_info_585_);
v_rawVal_586_ = lean_ctor_get(v_x_559_, 1);
lean_inc_ref(v_rawVal_586_);
v_val_587_ = lean_ctor_get(v_x_559_, 2);
lean_inc(v_val_587_);
v_preresolved_588_ = lean_ctor_get(v_x_559_, 3);
lean_inc(v_preresolved_588_);
lean_dec_ref_known(v_x_559_, 4);
v_info_589_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_info_589_);
v_rawVal_590_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_rawVal_590_);
v_val_591_ = lean_ctor_get(v_x_560_, 2);
lean_inc(v_val_591_);
v_preresolved_592_ = lean_ctor_get(v_x_560_, 3);
lean_inc(v_preresolved_592_);
lean_dec_ref_known(v_x_560_, 4);
v___x_597_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_585_, v_info_589_);
if (v___x_597_ == 0)
{
lean_dec_ref(v_rawVal_590_);
lean_dec_ref(v_rawVal_586_);
v___y_594_ = v___x_597_;
goto v___jp_593_;
}
else
{
uint8_t v___x_598_; 
v___x_598_ = l_Substring_Raw_beq(v_rawVal_586_, v_rawVal_590_);
v___y_594_ = v___x_598_;
goto v___jp_593_;
}
v___jp_593_:
{
if (v___y_594_ == 0)
{
lean_dec(v_preresolved_592_);
lean_dec(v_val_591_);
lean_dec(v_preresolved_588_);
lean_dec(v_val_587_);
return v___y_594_;
}
else
{
uint8_t v___x_595_; 
v___x_595_ = lean_name_eq(v_val_587_, v_val_591_);
lean_dec(v_val_591_);
lean_dec(v_val_587_);
if (v___x_595_ == 0)
{
lean_dec(v_preresolved_592_);
lean_dec(v_preresolved_588_);
return v___x_595_;
}
else
{
uint8_t v___x_596_; 
v___x_596_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_588_, v_preresolved_592_);
lean_dec(v_preresolved_592_);
lean_dec(v_preresolved_588_);
return v___x_596_;
}
}
}
}
else
{
uint8_t v___x_599_; 
lean_dec_ref_known(v_x_559_, 4);
lean_dec(v_x_560_);
v___x_599_ = 0;
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object* v_xs_600_, lean_object* v_ys_601_, lean_object* v_x_602_){
_start:
{
lean_object* v_zero_603_; uint8_t v_isZero_604_; 
v_zero_603_ = lean_unsigned_to_nat(0u);
v_isZero_604_ = lean_nat_dec_eq(v_x_602_, v_zero_603_);
if (v_isZero_604_ == 1)
{
lean_dec(v_x_602_);
return v_isZero_604_;
}
else
{
lean_object* v_one_605_; lean_object* v_n_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_one_605_ = lean_unsigned_to_nat(1u);
v_n_606_ = lean_nat_sub(v_x_602_, v_one_605_);
lean_dec(v_x_602_);
v___x_607_ = lean_array_fget_borrowed(v_xs_600_, v_n_606_);
v___x_608_ = lean_array_fget_borrowed(v_ys_601_, v_n_606_);
lean_inc(v___x_608_);
lean_inc(v___x_607_);
v___x_609_ = l_Lean_Syntax_eqWithInfo(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v_n_606_);
return v___x_609_;
}
else
{
v_x_602_ = v_n_606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object* v_xs_611_, lean_object* v_ys_612_, lean_object* v_x_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_611_, v_ys_612_, v_x_613_);
lean_dec_ref(v_ys_612_);
lean_dec_ref(v_xs_611_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_Lean_Syntax_eqWithInfo(v_x_616_, v_x_617_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object* v_xs_620_, lean_object* v_ys_621_, lean_object* v_hsz_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_620_, v_ys_621_, v_x_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object* v_xs_626_, lean_object* v_ys_627_, lean_object* v_hsz_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_626_, v_ys_627_, v_hsz_628_, v_x_629_, v_x_630_);
lean_dec_ref(v_ys_627_);
lean_dec_ref(v_xs_626_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object* v_opts_633_, lean_object* v_stx1_634_, lean_object* v_stx2_635_){
_start:
{
uint8_t v___x_636_; uint8_t v___x_637_; 
lean_inc(v_stx2_635_);
lean_inc(v_stx1_634_);
v___x_636_ = l_Lean_Syntax_eqWithInfo(v_stx1_634_, v_stx2_635_);
v___x_637_ = 1;
if (v___x_636_ == 0)
{
lean_object* v_map_638_; lean_object* v___x_639_; lean_object* v___f_640_; uint8_t v___y_642_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_map_638_ = lean_ctor_get(v_opts_633_, 0);
v___x_639_ = lean_box(v___x_636_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_640_, 0, v___x_639_);
v___x_657_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_658_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_638_, v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
v___y_642_ = v___x_636_;
goto v___jp_641_;
}
else
{
lean_object* v_val_659_; 
v_val_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_val_659_);
lean_dec_ref_known(v___x_658_, 1);
if (lean_obj_tag(v_val_659_) == 1)
{
uint8_t v_v_660_; 
v_v_660_ = lean_ctor_get_uint8(v_val_659_, 0);
lean_dec_ref_known(v_val_659_, 0);
v___y_642_ = v_v_660_;
goto v___jp_641_;
}
else
{
lean_dec(v_val_659_);
v___y_642_ = v___x_636_;
goto v___jp_641_;
}
}
v___jp_641_:
{
if (v___y_642_ == 0)
{
lean_dec_ref(v___f_640_);
lean_dec(v_stx2_635_);
lean_dec(v_stx1_634_);
return v___x_636_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_643_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0));
v___x_644_ = lean_box(0);
v___x_645_ = l_Lean_Syntax_formatStx(v_stx1_634_, v___x_644_, v___x_637_);
v___x_646_ = l_Std_Format_defWidth;
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = l_Std_Format_pretty(v___x_645_, v___x_646_, v___x_647_, v___x_647_);
v___x_649_ = lean_string_append(v___x_643_, v___x_648_);
lean_dec_ref(v___x_648_);
v___x_650_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1));
v___x_651_ = lean_string_append(v___x_649_, v___x_650_);
v___x_652_ = l_Lean_Syntax_formatStx(v_stx2_635_, v___x_644_, v___x_637_);
v___x_653_ = l_Std_Format_pretty(v___x_652_, v___x_646_, v___x_647_, v___x_647_);
v___x_654_ = lean_string_append(v___x_651_, v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = lean_dbg_trace(v___x_654_, v___f_640_);
v___x_656_ = lean_unbox(v___x_655_);
lean_dec(v___x_655_);
return v___x_656_;
}
}
}
else
{
lean_dec(v_stx2_635_);
lean_dec(v_stx1_634_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object* v_opts_661_, lean_object* v_stx1_662_, lean_object* v_stx2_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_661_, v_stx1_662_, v_stx2_663_);
lean_dec_ref(v_opts_661_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_667_) == 2)
{
lean_object* v_val_668_; 
v_val_668_ = lean_ctor_get(v_x_667_, 1);
lean_inc_ref(v_val_668_);
return v_val_668_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Syntax_getAtomVal(v_x_670_);
lean_dec(v_x_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_672_) == 2)
{
lean_object* v_info_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
v_info_674_ = lean_ctor_get(v_x_672_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v_x_672_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v_x_672_, 1);
lean_dec(v_unused_682_);
v___x_676_ = v_x_672_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_info_674_);
lean_dec(v_x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v_x_673_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_info_674_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_x_673_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_dec_ref(v_x_673_);
return v_x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object* v_stx_683_, lean_object* v_hyes_684_, lean_object* v_hno_685_){
_start:
{
if (lean_obj_tag(v_stx_683_) == 1)
{
lean_object* v___x_686_; 
lean_dec(v_hno_685_);
v___x_686_ = lean_apply_1(v_hyes_684_, v_stx_683_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_hyes_684_);
lean_dec(v_stx_683_);
v___x_687_ = lean_box(0);
v___x_688_ = lean_apply_1(v_hno_685_, v___x_687_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object* v_00_u03b2_689_, lean_object* v_stx_690_, lean_object* v_hyes_691_, lean_object* v_hno_692_){
_start:
{
if (lean_obj_tag(v_stx_690_) == 1)
{
lean_object* v___x_693_; 
lean_dec(v_hno_692_);
v___x_693_ = lean_apply_1(v_hyes_691_, v_stx_690_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_dec(v_hyes_691_);
lean_dec(v_stx_690_);
v___x_694_ = lean_box(0);
v___x_695_ = lean_apply_1(v_hno_692_, v___x_694_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object* v_stx_696_, lean_object* v_kind_697_, lean_object* v_hyes_698_, lean_object* v_hno_699_){
_start:
{
if (lean_obj_tag(v_stx_696_) == 1)
{
lean_object* v_kind_700_; uint8_t v___x_701_; 
v_kind_700_ = lean_ctor_get(v_stx_696_, 1);
v___x_701_ = lean_name_eq(v_kind_700_, v_kind_697_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec_ref_known(v_stx_696_, 3);
lean_dec(v_hyes_698_);
v___x_702_ = lean_box(0);
v___x_703_ = lean_apply_1(v_hno_699_, v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec(v_hno_699_);
v___x_704_ = lean_apply_1(v_hyes_698_, v_stx_696_);
return v___x_704_;
}
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; 
lean_dec(v_hyes_698_);
lean_dec(v_stx_696_);
v___x_705_ = lean_box(0);
v___x_706_ = lean_apply_1(v_hno_699_, v___x_705_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object* v_stx_707_, lean_object* v_kind_708_, lean_object* v_hyes_709_, lean_object* v_hno_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Syntax_ifNodeKind___redArg(v_stx_707_, v_kind_708_, v_hyes_709_, v_hno_710_);
lean_dec(v_kind_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object* v_00_u03b2_712_, lean_object* v_stx_713_, lean_object* v_kind_714_, lean_object* v_hyes_715_, lean_object* v_hno_716_){
_start:
{
if (lean_obj_tag(v_stx_713_) == 1)
{
lean_object* v_kind_717_; uint8_t v___x_718_; 
v_kind_717_ = lean_ctor_get(v_stx_713_, 1);
v___x_718_ = lean_name_eq(v_kind_717_, v_kind_714_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec_ref_known(v_stx_713_, 3);
lean_dec(v_hyes_715_);
v___x_719_ = lean_box(0);
v___x_720_ = lean_apply_1(v_hno_716_, v___x_719_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; 
lean_dec(v_hno_716_);
v___x_721_ = lean_apply_1(v_hyes_715_, v_stx_713_);
return v___x_721_;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v_hyes_715_);
lean_dec(v_stx_713_);
v___x_722_ = lean_box(0);
v___x_723_ = lean_apply_1(v_hno_716_, v___x_722_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object* v_00_u03b2_724_, lean_object* v_stx_725_, lean_object* v_kind_726_, lean_object* v_hyes_727_, lean_object* v_hno_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Syntax_ifNodeKind(v_00_u03b2_724_, v_stx_725_, v_kind_726_, v_hyes_727_, v_hno_728_);
lean_dec(v_kind_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_739_) == 1)
{
lean_inc_ref(v_x_739_);
return v_x_739_;
}
else
{
lean_object* v___x_740_; 
v___x_740_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Syntax_asNode(v_x_741_);
lean_dec(v_x_741_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object* v_stx_743_, lean_object* v_i_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = l_Lean_Syntax_getArg(v_stx_743_, v_i_744_);
v___x_746_ = l_Lean_Syntax_getId(v___x_745_);
lean_dec(v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* v_stx_747_, lean_object* v_i_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Syntax_getIdAt(v_stx_747_, v_i_748_);
lean_dec(v_i_748_);
lean_dec(v_stx_747_);
return v_res_749_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object* v_id_750_, lean_object* v_x_751_){
_start:
{
switch(lean_obj_tag(v_x_751_))
{
case 3:
{
lean_object* v_val_752_; uint8_t v___x_753_; 
v_val_752_ = lean_ctor_get(v_x_751_, 2);
v___x_753_ = lean_name_eq(v_id_750_, v_val_752_);
return v___x_753_;
}
case 1:
{
lean_object* v_args_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_args_754_ = lean_ctor_get(v_x_751_, 2);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_array_get_size(v_args_754_);
v___x_757_ = lean_nat_dec_lt(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
return v___x_757_;
}
else
{
if (v___x_757_ == 0)
{
return v___x_757_;
}
else
{
size_t v___x_758_; size_t v___x_759_; uint8_t v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_756_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_750_, v_args_754_, v___x_758_, v___x_759_);
return v___x_760_;
}
}
}
default: 
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object* v_id_762_, lean_object* v_as_763_, size_t v_i_764_, size_t v_stop_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_eq(v_i_764_, v_stop_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = lean_array_uget_borrowed(v_as_763_, v_i_764_);
v___x_768_ = l_Lean_Syntax_hasIdent(v_id_762_, v___x_767_);
if (v___x_768_ == 0)
{
size_t v___x_769_; size_t v___x_770_; 
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_764_, v___x_769_);
v_i_764_ = v___x_770_;
goto _start;
}
else
{
return v___x_768_;
}
}
else
{
uint8_t v___x_772_; 
v___x_772_ = 0;
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object* v_id_773_, lean_object* v_as_774_, lean_object* v_i_775_, lean_object* v_stop_776_){
_start:
{
size_t v_i_boxed_777_; size_t v_stop_boxed_778_; uint8_t v_res_779_; lean_object* v_r_780_; 
v_i_boxed_777_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_stop_boxed_778_ = lean_unbox_usize(v_stop_776_);
lean_dec(v_stop_776_);
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_773_, v_as_774_, v_i_boxed_777_, v_stop_boxed_778_);
lean_dec_ref(v_as_774_);
lean_dec(v_id_773_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object* v_id_781_, lean_object* v_x_782_){
_start:
{
uint8_t v_res_783_; lean_object* v_r_784_; 
v_res_783_ = l_Lean_Syntax_hasIdent(v_id_781_, v_x_782_);
lean_dec(v_x_782_);
lean_dec(v_id_781_);
v_r_784_ = lean_box(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object* v_stx_785_, lean_object* v_fn_786_){
_start:
{
if (lean_obj_tag(v_stx_785_) == 1)
{
lean_object* v_info_787_; lean_object* v_kind_788_; lean_object* v_args_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_info_787_ = lean_ctor_get(v_stx_785_, 0);
v_kind_788_ = lean_ctor_get(v_stx_785_, 1);
v_args_789_ = lean_ctor_get(v_stx_785_, 2);
v_isSharedCheck_797_ = !lean_is_exclusive(v_stx_785_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v_stx_785_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_args_789_);
lean_inc(v_kind_788_);
lean_inc(v_info_787_);
lean_dec(v_stx_785_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_apply_1(v_fn_786_, v_args_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 2, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_info_787_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_kind_788_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_dec_ref(v_fn_786_);
return v_stx_785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object* v_stx_798_, lean_object* v_i_799_, lean_object* v_fn_800_){
_start:
{
if (lean_obj_tag(v_stx_798_) == 1)
{
lean_object* v_info_801_; lean_object* v_kind_802_; lean_object* v_args_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_info_801_ = lean_ctor_get(v_stx_798_, 0);
v_kind_802_ = lean_ctor_get(v_stx_798_, 1);
v_args_803_ = lean_ctor_get(v_stx_798_, 2);
v___x_804_ = lean_array_get_size(v_args_803_);
v___x_805_ = lean_nat_dec_lt(v_i_799_, v___x_804_);
if (v___x_805_ == 0)
{
lean_dec_ref(v_fn_800_);
return v_stx_798_;
}
else
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_817_; 
lean_inc_ref(v_args_803_);
lean_inc(v_kind_802_);
lean_inc(v_info_801_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_stx_798_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_818_ = lean_ctor_get(v_stx_798_, 2);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_stx_798_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_stx_798_, 0);
lean_dec(v_unused_820_);
v___x_807_ = v_stx_798_;
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_stx_798_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v_v_809_; lean_object* v___x_810_; lean_object* v_xs_x27_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v_v_809_ = lean_array_fget(v_args_803_, v_i_799_);
v___x_810_ = lean_box(0);
v_xs_x27_811_ = lean_array_fset(v_args_803_, v_i_799_, v___x_810_);
v___x_812_ = lean_apply_1(v_fn_800_, v_v_809_);
v___x_813_ = lean_array_fset(v_xs_x27_811_, v_i_799_, v___x_812_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 2, v___x_813_);
v___x_815_ = v___x_807_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_info_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_kind_802_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_dec_ref(v_fn_800_);
return v_stx_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* v_stx_821_, lean_object* v_i_822_, lean_object* v_fn_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Syntax_modifyArg(v_stx_821_, v_i_822_, v_fn_823_);
lean_dec(v_i_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object* v_info_825_, lean_object* v_kind_826_, lean_object* v_toPure_827_, lean_object* v_____do__lift_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_829_, 0, v_info_825_);
lean_ctor_set(v___x_829_, 1, v_kind_826_);
lean_ctor_set(v___x_829_, 2, v_____do__lift_828_);
v___x_830_ = lean_apply_2(v_toPure_827_, lean_box(0), v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object* v_toPure_831_, lean_object* v_x_832_, lean_object* v_o_833_){
_start:
{
if (lean_obj_tag(v_o_833_) == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_apply_2(v_toPure_831_, lean_box(0), v_x_832_);
return v___x_834_;
}
else
{
lean_object* v_val_835_; lean_object* v___x_836_; 
lean_dec(v_x_832_);
v_val_835_ = lean_ctor_get(v_o_833_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_o_833_, 1);
v___x_836_ = lean_apply_2(v_toPure_831_, lean_box(0), v_val_835_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object* v_inst_837_, lean_object* v_fn_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 1)
{
lean_object* v_toApplicative_840_; lean_object* v_toBind_841_; lean_object* v_toPure_842_; lean_object* v_info_843_; lean_object* v_kind_844_; lean_object* v_args_845_; lean_object* v___f_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_toApplicative_840_ = lean_ctor_get(v_inst_837_, 0);
v_toBind_841_ = lean_ctor_get(v_inst_837_, 1);
lean_inc_n(v_toBind_841_, 2);
v_toPure_842_ = lean_ctor_get(v_toApplicative_840_, 1);
lean_inc_n(v_toPure_842_, 2);
v_info_843_ = lean_ctor_get(v_x_839_, 0);
v_kind_844_ = lean_ctor_get(v_x_839_, 1);
v_args_845_ = lean_ctor_get(v_x_839_, 2);
lean_inc(v_kind_844_);
lean_inc(v_info_843_);
v___f_846_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_846_, 0, v_info_843_);
lean_closure_set(v___f_846_, 1, v_kind_844_);
lean_closure_set(v___f_846_, 2, v_toPure_842_);
lean_inc_ref(v_args_845_);
lean_inc(v_fn_838_);
v___f_847_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_847_, 0, v_inst_837_);
lean_closure_set(v___f_847_, 1, v_fn_838_);
lean_closure_set(v___f_847_, 2, v_args_845_);
lean_closure_set(v___f_847_, 3, v_toBind_841_);
lean_closure_set(v___f_847_, 4, v___f_846_);
lean_closure_set(v___f_847_, 5, v_toPure_842_);
v___x_848_ = lean_apply_1(v_fn_838_, v_x_839_);
v___x_849_ = lean_apply_4(v_toBind_841_, lean_box(0), lean_box(0), v___x_848_, v___f_847_);
return v___x_849_;
}
else
{
lean_object* v_toApplicative_850_; lean_object* v_toBind_851_; lean_object* v_toPure_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_toApplicative_850_ = lean_ctor_get(v_inst_837_, 0);
lean_inc_ref(v_toApplicative_850_);
v_toBind_851_ = lean_ctor_get(v_inst_837_, 1);
lean_inc(v_toBind_851_);
lean_dec_ref(v_inst_837_);
v_toPure_852_ = lean_ctor_get(v_toApplicative_850_, 1);
lean_inc(v_toPure_852_);
lean_dec_ref(v_toApplicative_850_);
lean_inc(v_x_839_);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_853_, 0, v_toPure_852_);
lean_closure_set(v___f_853_, 1, v_x_839_);
v___x_854_ = lean_apply_1(v_fn_838_, v_x_839_);
v___x_855_ = lean_apply_4(v_toBind_851_, lean_box(0), lean_box(0), v___x_854_, v___f_853_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object* v_inst_856_, lean_object* v_fn_857_, lean_object* v_args_858_, lean_object* v_toBind_859_, lean_object* v___f_860_, lean_object* v_toPure_861_, lean_object* v_____do__lift_862_){
_start:
{
if (lean_obj_tag(v_____do__lift_862_) == 0)
{
lean_object* v___x_863_; size_t v_sz_864_; size_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v_toPure_861_);
lean_inc_ref(v_inst_856_);
v___x_863_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg), 3, 2);
lean_closure_set(v___x_863_, 0, v_inst_856_);
lean_closure_set(v___x_863_, 1, v_fn_857_);
v_sz_864_ = lean_array_size(v_args_858_);
v___x_865_ = ((size_t)0ULL);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_856_, v___x_863_, v_sz_864_, v___x_865_, v_args_858_);
v___x_867_ = lean_apply_4(v_toBind_859_, lean_box(0), lean_box(0), v___x_866_, v___f_860_);
return v___x_867_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_869_; 
lean_dec(v___f_860_);
lean_dec(v_toBind_859_);
lean_dec_ref(v_args_858_);
lean_dec(v_fn_857_);
lean_dec_ref(v_inst_856_);
v_val_868_ = lean_ctor_get(v_____do__lift_862_, 0);
lean_inc(v_val_868_);
lean_dec_ref_known(v_____do__lift_862_, 1);
v___x_869_ = lean_apply_2(v_toPure_861_, lean_box(0), v_val_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object* v_m_870_, lean_object* v_inst_871_, lean_object* v_fn_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Syntax_replaceM___redArg(v_inst_871_, v_fn_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object* v_info_875_, lean_object* v_kind_876_, lean_object* v_fn_877_, lean_object* v_args_878_){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_879_, 0, v_info_875_);
lean_ctor_set(v___x_879_, 1, v_kind_876_);
lean_ctor_set(v___x_879_, 2, v_args_878_);
v___x_880_ = lean_apply_1(v_fn_877_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object* v_inst_881_, lean_object* v_fn_882_, lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 1)
{
lean_object* v_toBind_884_; lean_object* v_info_885_; lean_object* v_kind_886_; lean_object* v_args_887_; lean_object* v___f_888_; lean_object* v___x_889_; size_t v_sz_890_; size_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_toBind_884_ = lean_ctor_get(v_inst_881_, 1);
lean_inc(v_toBind_884_);
v_info_885_ = lean_ctor_get(v_x_883_, 0);
lean_inc(v_info_885_);
v_kind_886_ = lean_ctor_get(v_x_883_, 1);
lean_inc(v_kind_886_);
v_args_887_ = lean_ctor_get(v_x_883_, 2);
lean_inc_ref(v_args_887_);
lean_dec_ref_known(v_x_883_, 3);
lean_inc(v_fn_882_);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_888_, 0, v_info_885_);
lean_closure_set(v___f_888_, 1, v_kind_886_);
lean_closure_set(v___f_888_, 2, v_fn_882_);
lean_inc_ref(v_inst_881_);
v___x_889_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg), 3, 2);
lean_closure_set(v___x_889_, 0, v_inst_881_);
lean_closure_set(v___x_889_, 1, v_fn_882_);
v_sz_890_ = lean_array_size(v_args_887_);
v___x_891_ = ((size_t)0ULL);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_881_, v___x_889_, v_sz_890_, v___x_891_, v_args_887_);
v___x_893_ = lean_apply_4(v_toBind_884_, lean_box(0), lean_box(0), v___x_892_, v___f_888_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
lean_dec_ref(v_inst_881_);
v___x_894_ = lean_apply_1(v_fn_882_, v_x_883_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* v_m_895_, lean_object* v_inst_896_, lean_object* v_fn_897_, lean_object* v_x_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_896_, v_fn_897_, v_x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object* v_fn_900_, lean_object* v_x_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lean_apply_1(v_fn_900_, v_x_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* v_fn_922_, lean_object* v_stx_923_){
_start:
{
lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___f_924_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUp___lam__0), 2, 1);
lean_closure_set(v___f_924_, 0, v_fn_922_);
v___x_925_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUp___closed__9));
v___x_926_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_925_, v___f_924_, v_stx_923_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v_leading_930_; lean_object* v_trailing_931_; lean_object* v_pos_932_; lean_object* v_endPos_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_960_; 
v_leading_930_ = lean_ctor_get(v_x_927_, 0);
v_trailing_931_ = lean_ctor_get(v_x_927_, 2);
v_pos_932_ = lean_ctor_get(v_x_927_, 1);
v_endPos_933_ = lean_ctor_get(v_x_927_, 3);
v_isSharedCheck_960_ = !lean_is_exclusive(v_x_927_);
if (v_isSharedCheck_960_ == 0)
{
v___x_935_ = v_x_927_;
v_isShared_936_ = v_isSharedCheck_960_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_endPos_933_);
lean_inc(v_trailing_931_);
lean_inc(v_pos_932_);
lean_inc(v_leading_930_);
lean_dec(v_x_927_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_960_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_str_937_; lean_object* v_stopPos_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_958_; 
v_str_937_ = lean_ctor_get(v_leading_930_, 0);
v_stopPos_938_ = lean_ctor_get(v_leading_930_, 2);
v_isSharedCheck_958_ = !lean_is_exclusive(v_leading_930_);
if (v_isSharedCheck_958_ == 0)
{
lean_object* v_unused_959_; 
v_unused_959_ = lean_ctor_get(v_leading_930_, 1);
lean_dec(v_unused_959_);
v___x_940_ = v_leading_930_;
v_isShared_941_ = v_isSharedCheck_958_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_stopPos_938_);
lean_inc(v_str_937_);
lean_dec(v_leading_930_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_958_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_str_942_; lean_object* v_startPos_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_956_; 
v_str_942_ = lean_ctor_get(v_trailing_931_, 0);
v_startPos_943_ = lean_ctor_get(v_trailing_931_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_trailing_931_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_trailing_931_, 2);
lean_dec(v_unused_957_);
v___x_945_ = v_trailing_931_;
v_isShared_946_ = v_isSharedCheck_956_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_startPos_943_);
lean_inc(v_str_942_);
lean_dec(v_trailing_931_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_956_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 2, v_stopPos_938_);
lean_ctor_set(v___x_945_, 1, v_x_928_);
lean_ctor_set(v___x_945_, 0, v_str_937_);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_str_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_x_928_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_stopPos_938_);
v___x_948_ = v_reuseFailAlloc_955_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 2, v_x_929_);
lean_ctor_set(v___x_940_, 1, v_startPos_943_);
lean_ctor_set(v___x_940_, 0, v_str_942_);
v___x_950_ = v___x_940_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_str_942_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_startPos_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_x_929_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_952_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 2, v___x_950_);
lean_ctor_set(v___x_935_, 0, v___x_948_);
v___x_952_ = v___x_935_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_pos_932_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v_endPos_933_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_929_);
lean_dec(v_x_928_);
return v_x_927_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v___x_963_, lean_object* v_a_964_, lean_object* v_b_965_){
_start:
{
lean_object* v___x_966_; uint8_t v_decide_967_; 
v___x_966_ = lean_nat_sub(v___x_961_, v___x_962_);
v_decide_967_ = lean_nat_dec_eq(v_a_964_, v___x_966_);
lean_dec(v___x_966_);
if (v_decide_967_ == 0)
{
uint32_t v___x_968_; lean_object* v___x_969_; uint32_t v___x_970_; uint8_t v___x_971_; 
v___x_968_ = 10;
v___x_969_ = lean_nat_add(v___x_962_, v_a_964_);
v___x_970_ = lean_string_utf8_get_fast(v___x_963_, v___x_969_);
v___x_971_ = lean_uint32_dec_eq(v___x_970_, v___x_968_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_a_964_);
v___x_972_ = lean_box(0);
v___x_973_ = lean_string_utf8_next_fast(v___x_963_, v___x_969_);
lean_dec(v___x_969_);
v___x_974_ = lean_nat_sub(v___x_973_, v___x_962_);
v_a_964_ = v___x_974_;
v_b_965_ = v___x_972_;
goto _start;
}
else
{
lean_object* v___x_976_; 
lean_dec(v___x_969_);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v_a_964_);
return v___x_976_;
}
}
else
{
lean_dec(v_a_964_);
lean_inc(v_b_965_);
return v_b_965_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v___x_979_, lean_object* v_a_980_, lean_object* v_b_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_977_, v___x_978_, v___x_979_, v_a_980_, v_b_981_);
lean_dec(v_b_981_);
lean_dec_ref(v___x_979_);
lean_dec(v___x_978_);
lean_dec(v___x_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_983_){
_start:
{
lean_object* v_str_984_; lean_object* v_startPos_985_; lean_object* v_stopPos_986_; uint8_t v___y_988_; uint8_t v___x_998_; uint8_t v___y_1000_; uint8_t v___x_1001_; 
v_str_984_ = lean_ctor_get(v_trail_983_, 0);
v_startPos_985_ = lean_ctor_get(v_trail_983_, 1);
v_stopPos_986_ = lean_ctor_get(v_trail_983_, 2);
v___x_998_ = lean_string_is_valid_pos(v_str_984_, v_startPos_985_);
v___x_1001_ = lean_string_is_valid_pos(v_str_984_, v_stopPos_986_);
if (v___x_1001_ == 0)
{
v___y_1000_ = v___x_1001_;
goto v___jp_999_;
}
else
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_nat_dec_le(v_startPos_985_, v_stopPos_986_);
v___y_1000_ = v___x_1002_;
goto v___jp_999_;
}
v___jp_987_:
{
if (v___y_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_nat_sub(v_stopPos_986_, v_startPos_985_);
v___x_990_ = lean_nat_add(v_startPos_985_, v___x_989_);
lean_dec(v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_searcher_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_searcher_991_ = lean_unsigned_to_nat(0u);
v___x_992_ = lean_box(0);
v___x_993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v_stopPos_986_, v_startPos_985_, v_str_984_, v_searcher_991_, v___x_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_nat_sub(v_stopPos_986_, v_startPos_985_);
v___x_995_ = lean_nat_add(v_startPos_985_, v___x_994_);
lean_dec(v___x_994_);
return v___x_995_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_997_; 
v_val_996_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v___x_993_, 1);
v___x_997_ = lean_nat_add(v_startPos_985_, v_val_996_);
lean_dec(v_val_996_);
return v___x_997_;
}
}
}
v___jp_999_:
{
if (v___x_998_ == 0)
{
v___y_988_ = v___x_998_;
goto v___jp_987_;
}
else
{
v___y_988_ = v___y_1000_;
goto v___jp_987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object* v_trail_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trail_1003_);
lean_dec_ref(v_trail_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v_inst_1009_, lean_object* v_R_1010_, lean_object* v_a_1011_, lean_object* v_b_1012_, lean_object* v_c_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1005_, v___x_1006_, v___x_1008_, v_a_1011_, v_b_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1015_, lean_object* v___x_1016_, lean_object* v___x_1017_, lean_object* v___x_1018_, lean_object* v_inst_1019_, lean_object* v_R_1020_, lean_object* v_a_1021_, lean_object* v_b_1022_, lean_object* v_c_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1015_, v___x_1016_, v___x_1017_, v___x_1018_, v_inst_1019_, v_R_1020_, v_a_1021_, v_b_1022_, v_c_1023_);
lean_dec(v_b_1022_);
lean_dec_ref(v___x_1018_);
lean_dec_ref(v___x_1017_);
lean_dec(v___x_1016_);
lean_dec(v___x_1015_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___y_1028_; 
switch(lean_obj_tag(v_x_1025_))
{
case 2:
{
lean_object* v_info_1031_; 
v_info_1031_ = lean_ctor_get(v_x_1025_, 0);
lean_inc(v_info_1031_);
if (lean_obj_tag(v_info_1031_) == 0)
{
lean_object* v_val_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1044_; 
v_val_1032_ = lean_ctor_get(v_x_1025_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v_x_1025_, 0);
lean_dec(v_unused_1045_);
v___x_1034_ = v_x_1025_;
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_val_1032_);
lean_dec(v_x_1025_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_trailing_1036_; lean_object* v_trailStop_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v_trailing_1036_ = lean_ctor_get(v_info_1031_, 2);
v_trailStop_1037_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1036_);
lean_inc(v_trailStop_1037_);
v___x_1038_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1031_, v_a_1026_, v_trailStop_1037_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1038_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_val_1032_);
v___x_1040_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_trailStop_1037_);
return v___x_1042_;
}
}
}
else
{
lean_dec_ref_known(v_x_1025_, 2);
lean_dec(v_info_1031_);
v___y_1028_ = v_a_1026_;
goto v___jp_1027_;
}
}
case 3:
{
lean_object* v_info_1046_; 
v_info_1046_ = lean_ctor_get(v_x_1025_, 0);
lean_inc(v_info_1046_);
if (lean_obj_tag(v_info_1046_) == 0)
{
lean_object* v_rawVal_1047_; lean_object* v_val_1048_; lean_object* v_preresolved_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1061_; 
v_rawVal_1047_ = lean_ctor_get(v_x_1025_, 1);
v_val_1048_ = lean_ctor_get(v_x_1025_, 2);
v_preresolved_1049_ = lean_ctor_get(v_x_1025_, 3);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1025_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_x_1025_, 0);
lean_dec(v_unused_1062_);
v___x_1051_ = v_x_1025_;
v_isShared_1052_ = v_isSharedCheck_1061_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_preresolved_1049_);
lean_inc(v_val_1048_);
lean_inc(v_rawVal_1047_);
lean_dec(v_x_1025_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1061_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v_trailing_1053_; lean_object* v_trailStop_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v_trailing_1053_ = lean_ctor_get(v_info_1046_, 2);
v_trailStop_1054_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1053_);
lean_inc(v_trailStop_1054_);
v___x_1055_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1046_, v_a_1026_, v_trailStop_1054_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1055_);
v___x_1057_ = v___x_1051_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_rawVal_1047_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_val_1048_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_preresolved_1049_);
v___x_1057_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v_trailStop_1054_);
return v___x_1059_;
}
}
}
else
{
lean_dec_ref_known(v_x_1025_, 4);
lean_dec(v_info_1046_);
v___y_1028_ = v_a_1026_;
goto v___jp_1027_;
}
}
default: 
{
lean_dec(v_x_1025_);
v___y_1028_ = v_a_1026_;
goto v___jp_1027_;
}
}
v___jp_1027_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___y_1028_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
switch(lean_obj_tag(v___y_1063_))
{
case 2:
{
lean_object* v_info_1068_; 
v_info_1068_ = lean_ctor_get(v___y_1063_, 0);
lean_inc(v_info_1068_);
if (lean_obj_tag(v_info_1068_) == 0)
{
lean_object* v_val_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1081_; 
v_val_1069_ = lean_ctor_get(v___y_1063_, 1);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___y_1063_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___y_1063_, 0);
lean_dec(v_unused_1082_);
v___x_1071_ = v___y_1063_;
v_isShared_1072_ = v_isSharedCheck_1081_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_val_1069_);
lean_dec(v___y_1063_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1081_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_trailing_1073_; lean_object* v_trailStop_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v_trailing_1073_ = lean_ctor_get(v_info_1068_, 2);
v_trailStop_1074_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1073_);
lean_inc(v_trailStop_1074_);
v___x_1075_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1068_, v___y_1064_, v_trailStop_1074_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1075_);
v___x_1077_ = v___x_1071_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1075_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_val_1069_);
v___x_1077_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v_trailStop_1074_);
return v___x_1079_;
}
}
}
else
{
lean_dec(v_info_1068_);
lean_dec_ref_known(v___y_1063_, 2);
goto v___jp_1065_;
}
}
case 3:
{
lean_object* v_info_1083_; 
v_info_1083_ = lean_ctor_get(v___y_1063_, 0);
lean_inc(v_info_1083_);
if (lean_obj_tag(v_info_1083_) == 0)
{
lean_object* v_rawVal_1084_; lean_object* v_val_1085_; lean_object* v_preresolved_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1098_; 
v_rawVal_1084_ = lean_ctor_get(v___y_1063_, 1);
v_val_1085_ = lean_ctor_get(v___y_1063_, 2);
v_preresolved_1086_ = lean_ctor_get(v___y_1063_, 3);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___y_1063_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v___y_1063_, 0);
lean_dec(v_unused_1099_);
v___x_1088_ = v___y_1063_;
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_preresolved_1086_);
lean_inc(v_val_1085_);
lean_inc(v_rawVal_1084_);
lean_dec(v___y_1063_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1098_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_trailing_1090_; lean_object* v_trailStop_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v_trailing_1090_ = lean_ctor_get(v_info_1083_, 2);
v_trailStop_1091_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1090_);
lean_inc(v_trailStop_1091_);
v___x_1092_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1083_, v___y_1064_, v_trailStop_1091_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1092_);
v___x_1094_ = v___x_1088_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_rawVal_1084_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_val_1085_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_preresolved_1086_);
v___x_1094_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_trailStop_1091_);
return v___x_1096_;
}
}
}
else
{
lean_dec_ref_known(v___y_1063_, 4);
lean_dec(v_info_1083_);
goto v___jp_1065_;
}
}
default: 
{
lean_dec(v___y_1063_);
goto v___jp_1065_;
}
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___y_1064_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1100_, lean_object* v___y_1101_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 1)
{
lean_object* v_info_1102_; lean_object* v_kind_1103_; lean_object* v_args_1104_; lean_object* v___x_1105_; lean_object* v_fst_1106_; 
v_info_1102_ = lean_ctor_get(v_x_1100_, 0);
lean_inc(v_info_1102_);
v_kind_1103_ = lean_ctor_get(v_x_1100_, 1);
lean_inc(v_kind_1103_);
v_args_1104_ = lean_ctor_get(v_x_1100_, 2);
lean_inc_ref(v_args_1104_);
v___x_1105_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1100_, v___y_1101_);
v_fst_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_fst_1106_);
if (lean_obj_tag(v_fst_1106_) == 0)
{
lean_object* v_snd_1107_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; lean_object* v_fst_1111_; lean_object* v_snd_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
v_snd_1107_ = lean_ctor_get(v___x_1105_, 1);
lean_inc(v_snd_1107_);
lean_dec_ref(v___x_1105_);
v_sz_1108_ = lean_array_size(v_args_1104_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1108_, v___x_1109_, v_args_1104_, v_snd_1107_);
v_fst_1111_ = lean_ctor_get(v___x_1110_, 0);
v_snd_1112_ = lean_ctor_get(v___x_1110_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1114_ = v___x_1110_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_snd_1112_);
lean_inc(v_fst_1111_);
lean_dec(v___x_1110_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1116_, 0, v_info_1102_);
lean_ctor_set(v___x_1116_, 1, v_kind_1103_);
lean_ctor_set(v___x_1116_, 2, v_fst_1111_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v_snd_1112_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_snd_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_args_1104_);
lean_dec(v_kind_1103_);
lean_dec(v_info_1102_);
v_snd_1121_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1129_ == 0)
{
lean_object* v_unused_1130_; 
v_unused_1130_ = lean_ctor_get(v___x_1105_, 0);
lean_dec(v_unused_1130_);
v___x_1123_ = v___x_1105_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_snd_1121_);
lean_dec(v___x_1105_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_val_1125_; lean_object* v___x_1127_; 
v_val_1125_ = lean_ctor_get(v_fst_1106_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v_fst_1106_, 1);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v_val_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_val_1125_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_snd_1121_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v___x_1131_; lean_object* v_fst_1132_; 
lean_inc(v_x_1100_);
v___x_1131_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1100_, v___y_1101_);
v_fst_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_fst_1132_);
if (lean_obj_tag(v_fst_1132_) == 0)
{
lean_object* v_snd_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
v_snd_1133_ = lean_ctor_get(v___x_1131_, 1);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
lean_object* v_unused_1141_; 
v_unused_1141_ = lean_ctor_get(v___x_1131_, 0);
lean_dec(v_unused_1141_);
v___x_1135_ = v___x_1131_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_snd_1133_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v_x_1100_);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_x_1100_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_snd_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_object* v_snd_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
lean_dec(v_x_1100_);
v_snd_1142_ = lean_ctor_get(v___x_1131_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v___x_1131_, 0);
lean_dec(v_unused_1151_);
v___x_1144_ = v___x_1131_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snd_1142_);
lean_dec(v___x_1131_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_val_1146_; lean_object* v___x_1148_; 
v_val_1146_ = lean_ctor_get(v_fst_1132_, 0);
lean_inc(v_val_1146_);
lean_dec_ref_known(v_fst_1132_, 1);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v_val_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_val_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_snd_1142_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1152_, size_t v_i_1153_, lean_object* v_bs_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_usize_dec_lt(v_i_1153_, v_sz_1152_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_bs_1154_);
lean_ctor_set(v___x_1157_, 1, v___y_1155_);
return v___x_1157_;
}
else
{
lean_object* v_v_1158_; lean_object* v___x_1159_; lean_object* v_fst_1160_; lean_object* v_snd_1161_; lean_object* v___x_1162_; lean_object* v_bs_x27_1163_; size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
v_v_1158_ = lean_array_uget_borrowed(v_bs_1154_, v_i_1153_);
lean_inc(v_v_1158_);
v___x_1159_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1158_, v___y_1155_);
v_fst_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_fst_1160_);
v_snd_1161_ = lean_ctor_get(v___x_1159_, 1);
lean_inc(v_snd_1161_);
lean_dec_ref(v___x_1159_);
v___x_1162_ = lean_unsigned_to_nat(0u);
v_bs_x27_1163_ = lean_array_uset(v_bs_1154_, v_i_1153_, v___x_1162_);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1153_, v___x_1164_);
v___x_1166_ = lean_array_uset(v_bs_x27_1163_, v_i_1153_, v_fst_1160_);
v_i_1153_ = v___x_1165_;
v_bs_1154_ = v___x_1166_;
v___y_1155_ = v_snd_1161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1168_, lean_object* v_i_1169_, lean_object* v_bs_1170_, lean_object* v___y_1171_){
_start:
{
size_t v_sz_boxed_1172_; size_t v_i_boxed_1173_; lean_object* v_res_1174_; 
v_sz_boxed_1172_ = lean_unbox_usize(v_sz_1168_);
lean_dec(v_sz_1168_);
v_i_boxed_1173_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1172_, v_i_boxed_1173_, v_bs_1170_, v___y_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_fst_1178_; 
v___x_1176_ = lean_unsigned_to_nat(0u);
v___x_1177_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1175_, v___x_1176_);
v_fst_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_fst_1178_);
lean_dec_ref(v___x_1177_);
return v_fst_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1179_, lean_object* v_x_1180_){
_start:
{
switch(lean_obj_tag(v_x_1180_))
{
case 2:
{
lean_object* v_info_1181_; lean_object* v_val_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1190_; 
v_info_1181_ = lean_ctor_get(v_x_1180_, 0);
v_val_1182_ = lean_ctor_get(v_x_1180_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1184_ = v_x_1180_;
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_val_1182_);
lean_inc(v_info_1181_);
lean_dec(v_x_1180_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1190_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1179_, v_info_1181_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_val_1182_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
case 3:
{
lean_object* v_info_1191_; lean_object* v_rawVal_1192_; lean_object* v_val_1193_; lean_object* v_preresolved_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1202_; 
v_info_1191_ = lean_ctor_get(v_x_1180_, 0);
v_rawVal_1192_ = lean_ctor_get(v_x_1180_, 1);
v_val_1193_ = lean_ctor_get(v_x_1180_, 2);
v_preresolved_1194_ = lean_ctor_get(v_x_1180_, 3);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1196_ = v_x_1180_;
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_preresolved_1194_);
lean_inc(v_val_1193_);
lean_inc(v_rawVal_1192_);
lean_inc(v_info_1191_);
lean_dec(v_x_1180_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1202_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1179_, v_info_1191_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_rawVal_1192_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_val_1193_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_preresolved_1194_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
case 1:
{
lean_object* v_info_1203_; lean_object* v_kind_1204_; lean_object* v_args_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_info_1203_ = lean_ctor_get(v_x_1180_, 0);
v_kind_1204_ = lean_ctor_get(v_x_1180_, 1);
v_args_1205_ = lean_ctor_get(v_x_1180_, 2);
v___x_1206_ = lean_array_get_size(v_args_1205_);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_nat_dec_eq(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1220_; 
lean_inc_ref(v_args_1205_);
lean_inc(v_kind_1204_);
lean_inc(v_info_1203_);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; lean_object* v_unused_1222_; lean_object* v_unused_1223_; 
v_unused_1221_ = lean_ctor_get(v_x_1180_, 2);
lean_dec(v_unused_1221_);
v_unused_1222_ = lean_ctor_get(v_x_1180_, 1);
lean_dec(v_unused_1222_);
v_unused_1223_ = lean_ctor_get(v_x_1180_, 0);
lean_dec(v_unused_1223_);
v___x_1210_ = v_x_1180_;
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v_x_1180_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1220_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v_i_1213_; lean_object* v___x_1214_; lean_object* v_last_1215_; lean_object* v_args_1216_; lean_object* v___x_1218_; 
v___x_1212_ = lean_unsigned_to_nat(1u);
v_i_1213_ = lean_nat_sub(v___x_1206_, v___x_1212_);
v___x_1214_ = lean_array_fget_borrowed(v_args_1205_, v_i_1213_);
lean_inc(v___x_1214_);
v_last_1215_ = l_Lean_Syntax_updateTrailing(v_trailing_1179_, v___x_1214_);
v_args_1216_ = lean_array_fset(v_args_1205_, v_i_1213_, v_last_1215_);
lean_dec(v_i_1213_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 2, v_args_1216_);
v___x_1218_ = v___x_1210_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_info_1203_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_kind_1204_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_args_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_dec_ref(v_trailing_1179_);
return v_x_1180_;
}
}
default: 
{
lean_dec_ref(v_trailing_1179_);
return v_x_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_x_1224_, lean_object* v_x_1225_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
return v_x_1224_;
}
else
{
lean_object* v_head_1226_; lean_object* v_tail_1227_; lean_object* v___x_1228_; 
v_head_1226_ = lean_ctor_get(v_x_1225_, 0);
lean_inc(v_head_1226_);
v_tail_1227_ = lean_ctor_get(v_x_1225_, 1);
lean_inc(v_tail_1227_);
lean_dec_ref_known(v_x_1225_, 2);
v___x_1228_ = l_Lean_Name_append(v_x_1224_, v_head_1226_);
v_x_1224_ = v___x_1228_;
v_x_1225_ = v_tail_1227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1232_, lean_object* v_nFields_x3f_1233_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1233_) == 1)
{
lean_object* v_val_1234_; lean_object* v_nameComps_1235_; lean_object* v___x_1236_; lean_object* v_nPrefix_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_namePrefix_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_val_1234_ = lean_ctor_get(v_nFields_x3f_1233_, 0);
v_nameComps_1235_ = l_Lean_Name_components(v_n_1232_);
v___x_1236_ = l_List_lengthTR___redArg(v_nameComps_1235_);
v_nPrefix_1237_ = lean_nat_sub(v___x_1236_, v_val_1234_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_box(0);
v___x_1239_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1237_);
lean_inc(v_nameComps_1235_);
v___x_1240_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1235_, v_nameComps_1235_, v_nPrefix_1237_, v___x_1239_);
v_namePrefix_1241_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1238_, v___x_1240_);
v___x_1242_ = l_List_drop___redArg(v_nPrefix_1237_, v_nameComps_1235_);
lean_dec(v_nameComps_1235_);
v___x_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_namePrefix_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Name_components(v_n_1232_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___boxed(lean_object* v_n_1245_, lean_object* v_nFields_x3f_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_n_1245_, v_nFields_x3f_1246_);
lean_dec(v_nFields_x3f_1246_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(0);
v___x_1250_ = lean_panic_fn_borrowed(v___x_1249_, v_msg_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
return v_x_1251_;
}
else
{
lean_object* v_head_1253_; lean_object* v_tail_1254_; lean_object* v_startPos_1255_; lean_object* v_stopPos_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_head_1253_ = lean_ctor_get(v_x_1252_, 0);
v_tail_1254_ = lean_ctor_get(v_x_1252_, 1);
v_startPos_1255_ = lean_ctor_get(v_head_1253_, 1);
v_stopPos_1256_ = lean_ctor_get(v_head_1253_, 2);
v___x_1257_ = lean_nat_sub(v_stopPos_1256_, v_startPos_1255_);
v___x_1258_ = lean_nat_add(v_x_1251_, v___x_1257_);
lean_dec(v___x_1257_);
lean_dec(v_x_1251_);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_add(v___x_1258_, v___x_1259_);
lean_dec(v___x_1258_);
v_x_1251_ = v___x_1260_;
v_x_1252_ = v_tail_1254_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1262_, v_x_1263_);
lean_dec(v_x_1263_);
return v_res_1264_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1266_ = lean_string_utf8_byte_size(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1267_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___x_1268_);
lean_ctor_set(v___x_1270_, 2, v___x_1267_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1272_, lean_object* v_pos_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
if (lean_obj_tag(v_a_1274_) == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = l_List_reverse___redArg(v_a_1275_);
return v___x_1276_;
}
else
{
lean_object* v_head_1277_; lean_object* v_tail_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1296_; 
v_head_1277_ = lean_ctor_get(v_a_1274_, 0);
v_tail_1278_ = lean_ctor_get(v_a_1274_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_a_1274_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1280_ = v_a_1274_;
v_isShared_1281_ = v_isSharedCheck_1296_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_tail_1278_);
lean_inc(v_head_1277_);
lean_dec(v_a_1274_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1296_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v_stopPos_1282_; lean_object* v_startPos_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v_info_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v_stopPos_1282_ = lean_ctor_get(v_head_1277_, 2);
lean_inc(v_stopPos_1282_);
lean_dec(v_head_1277_);
v_startPos_1283_ = lean_ctor_get(v_rawVal_1272_, 1);
v___x_1284_ = lean_nat_sub(v_stopPos_1282_, v_startPos_1283_);
lean_dec(v_stopPos_1282_);
v___x_1285_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___x_1286_ = lean_nat_add(v___x_1284_, v_pos_1273_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v___x_1287_, v___x_1286_);
v_info_1289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1289_, 0, v___x_1285_);
lean_ctor_set(v_info_1289_, 1, v___x_1286_);
lean_ctor_set(v_info_1289_, 2, v___x_1285_);
lean_ctor_set(v_info_1289_, 3, v___x_1288_);
v___x_1290_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__2));
v___x_1291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_info_1289_);
lean_ctor_set(v___x_1291_, 1, v___x_1290_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v_a_1275_);
lean_ctor_set(v___x_1280_, 0, v___x_1291_);
v___x_1293_ = v___x_1280_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_a_1275_);
v___x_1293_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
v_a_1274_ = v_tail_1278_;
v_a_1275_ = v___x_1293_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1297_, lean_object* v_pos_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1297_, v_pos_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_pos_1298_);
lean_dec_ref(v_rawVal_1297_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1302_, lean_object* v_pos_1303_, lean_object* v_trailing_1304_, lean_object* v_leading_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
if (lean_obj_tag(v_a_1306_) == 0)
{
lean_object* v___x_1308_; 
lean_dec_ref(v_leading_1305_);
lean_dec_ref(v_trailing_1304_);
v___x_1308_ = l_List_reverse___redArg(v_a_1307_);
return v___x_1308_;
}
else
{
lean_object* v_head_1309_; lean_object* v_snd_1310_; lean_object* v_tail_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1341_; 
v_head_1309_ = lean_ctor_get(v_a_1306_, 0);
lean_inc(v_head_1309_);
v_snd_1310_ = lean_ctor_get(v_head_1309_, 1);
lean_inc(v_snd_1310_);
v_tail_1311_ = lean_ctor_get(v_a_1306_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_a_1306_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_a_1306_, 0);
lean_dec(v_unused_1342_);
v___x_1313_ = v_a_1306_;
v_isShared_1314_ = v_isSharedCheck_1341_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_tail_1311_);
lean_dec(v_a_1306_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1341_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v_fst_1315_; lean_object* v_startPos_1316_; lean_object* v_stopPos_1317_; lean_object* v_startPos_1318_; lean_object* v_stopPos_1319_; lean_object* v_off_1320_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1335_; lean_object* v___x_1338_; uint8_t v_decide_1339_; 
v_fst_1315_ = lean_ctor_get(v_head_1309_, 0);
lean_inc(v_fst_1315_);
lean_dec(v_head_1309_);
v_startPos_1316_ = lean_ctor_get(v_snd_1310_, 1);
v_stopPos_1317_ = lean_ctor_get(v_snd_1310_, 2);
v_startPos_1318_ = lean_ctor_get(v_rawVal_1302_, 1);
v_stopPos_1319_ = lean_ctor_get(v_rawVal_1302_, 2);
v_off_1320_ = lean_nat_sub(v_startPos_1316_, v_startPos_1318_);
v___x_1338_ = lean_unsigned_to_nat(0u);
v_decide_1339_ = lean_nat_dec_eq(v_off_1320_, v___x_1338_);
if (v_decide_1339_ == 0)
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___y_1335_ = v___x_1340_;
goto v___jp_1334_;
}
else
{
lean_inc_ref(v_leading_1305_);
v___y_1335_ = v_leading_1305_;
goto v___jp_1334_;
}
v___jp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_info_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1324_ = lean_nat_add(v_off_1320_, v_pos_1303_);
lean_dec(v_off_1320_);
v___x_1325_ = lean_nat_sub(v_stopPos_1317_, v_startPos_1316_);
v___x_1326_ = lean_nat_add(v___x_1325_, v___x_1324_);
lean_dec(v___x_1325_);
v_info_1327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1327_, 0, v___y_1322_);
lean_ctor_set(v_info_1327_, 1, v___x_1324_);
lean_ctor_set(v_info_1327_, 2, v___y_1323_);
lean_ctor_set(v_info_1327_, 3, v___x_1326_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1329_, 0, v_info_1327_);
lean_ctor_set(v___x_1329_, 1, v_snd_1310_);
lean_ctor_set(v___x_1329_, 2, v_fst_1315_);
lean_ctor_set(v___x_1329_, 3, v___x_1328_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v_a_1307_);
lean_ctor_set(v___x_1313_, 0, v___x_1329_);
v___x_1331_ = v___x_1313_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_a_1307_);
v___x_1331_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
v_a_1306_ = v_tail_1311_;
v_a_1307_ = v___x_1331_;
goto _start;
}
}
v___jp_1334_:
{
uint8_t v_decide_1336_; 
v_decide_1336_ = lean_nat_dec_eq(v_stopPos_1317_, v_stopPos_1319_);
if (v_decide_1336_ == 0)
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1, &l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1);
v___y_1322_ = v___y_1335_;
v___y_1323_ = v___x_1337_;
goto v___jp_1321_;
}
else
{
lean_inc_ref(v_trailing_1304_);
v___y_1322_ = v___y_1335_;
v___y_1323_ = v_trailing_1304_;
goto v___jp_1321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1343_, lean_object* v_pos_1344_, lean_object* v_trailing_1345_, lean_object* v_leading_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1343_, v_pos_1344_, v_trailing_1345_, v_leading_1346_, v_a_1347_, v_a_1348_);
lean_dec(v_pos_1344_);
lean_dec_ref(v_rawVal_1343_);
return v_res_1349_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__5(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1358_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1359_ = lean_unsigned_to_nat(9u);
v___x_1360_ = lean_unsigned_to_nat(342u);
v___x_1361_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1362_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1363_ = l_mkPanicMessageWithDecl(v___x_1362_, v___x_1361_, v___x_1360_, v___x_1359_, v___x_1358_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1364_, lean_object* v_nFields_x3f_1365_){
_start:
{
if (lean_obj_tag(v_stx_1364_) == 3)
{
lean_object* v_info_1366_; 
v_info_1366_ = lean_ctor_get(v_stx_1364_, 0);
lean_inc(v_info_1366_);
if (lean_obj_tag(v_info_1366_) == 0)
{
lean_object* v_rawVal_1367_; lean_object* v_val_1368_; lean_object* v_leading_1369_; lean_object* v_pos_1370_; lean_object* v_trailing_1371_; lean_object* v_rawComps_1372_; uint8_t v___x_1373_; 
v_rawVal_1367_ = lean_ctor_get(v_stx_1364_, 1);
lean_inc_ref_n(v_rawVal_1367_, 2);
v_val_1368_ = lean_ctor_get(v_stx_1364_, 2);
lean_inc(v_val_1368_);
lean_dec_ref_known(v_stx_1364_, 4);
v_leading_1369_ = lean_ctor_get(v_info_1366_, 0);
lean_inc_ref(v_leading_1369_);
v_pos_1370_ = lean_ctor_get(v_info_1366_, 1);
lean_inc(v_pos_1370_);
v_trailing_1371_ = lean_ctor_get(v_info_1366_, 2);
lean_inc_ref(v_trailing_1371_);
lean_dec_ref_known(v_info_1366_, 4);
v_rawComps_1372_ = l_Lean_Syntax_splitNameLit(v_rawVal_1367_);
v___x_1373_ = l_List_isEmpty___redArg(v_rawComps_1372_);
if (v___x_1373_ == 0)
{
lean_object* v_val_1374_; lean_object* v_nameComps_1375_; lean_object* v___y_1377_; 
v_val_1374_ = l_Lean_Name_eraseMacroScopes(v_val_1368_);
lean_dec(v_val_1368_);
v_nameComps_1375_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1374_, v_nFields_x3f_1365_);
if (lean_obj_tag(v_nFields_x3f_1365_) == 1)
{
lean_object* v_val_1391_; lean_object* v_str_1392_; lean_object* v_startPos_1393_; lean_object* v_stopPos_1394_; lean_object* v___x_1395_; lean_object* v_nPrefix_1396_; lean_object* v___y_1398_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v_prefixSz_1404_; lean_object* v___x_1405_; lean_object* v_prefixSz_1406_; lean_object* v___y_1408_; uint8_t v___x_1413_; 
v_val_1391_ = lean_ctor_get(v_nFields_x3f_1365_, 0);
v_str_1392_ = lean_ctor_get(v_rawVal_1367_, 0);
v_startPos_1393_ = lean_ctor_get(v_rawVal_1367_, 1);
v_stopPos_1394_ = lean_ctor_get(v_rawVal_1367_, 2);
v___x_1395_ = l_List_lengthTR___redArg(v_rawComps_1372_);
v_nPrefix_1396_ = lean_nat_sub(v___x_1395_, v_val_1391_);
lean_dec(v___x_1395_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
lean_inc(v_nPrefix_1396_);
lean_inc(v_rawComps_1372_);
v___x_1403_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1372_, v_rawComps_1372_, v_nPrefix_1396_, v___x_1402_);
v_prefixSz_1404_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1401_, v___x_1403_);
lean_dec(v___x_1403_);
v___x_1405_ = lean_unsigned_to_nat(1u);
v_prefixSz_1406_ = lean_nat_sub(v_prefixSz_1404_, v___x_1405_);
lean_dec(v_prefixSz_1404_);
v___x_1413_ = lean_nat_dec_le(v_prefixSz_1406_, v___x_1401_);
if (v___x_1413_ == 0)
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_nat_dec_le(v_stopPos_1394_, v_startPos_1393_);
if (v___x_1414_ == 0)
{
lean_inc(v_startPos_1393_);
v___y_1408_ = v_startPos_1393_;
goto v___jp_1407_;
}
else
{
lean_inc(v_stopPos_1394_);
v___y_1408_ = v_stopPos_1394_;
goto v___jp_1407_;
}
}
else
{
lean_object* v___x_1415_; 
lean_dec(v_prefixSz_1406_);
v___x_1415_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
v___y_1398_ = v___x_1415_;
goto v___jp_1397_;
}
v___jp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = l_List_drop___redArg(v_nPrefix_1396_, v_rawComps_1372_);
lean_dec(v_rawComps_1372_);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___y_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___y_1377_ = v___x_1400_;
goto v___jp_1376_;
}
v___jp_1407_:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1409_ = lean_nat_add(v_startPos_1393_, v_prefixSz_1406_);
lean_dec(v_prefixSz_1406_);
v___x_1410_ = lean_nat_dec_le(v_stopPos_1394_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_inc_ref(v_str_1392_);
v___x_1411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1411_, 0, v_str_1392_);
lean_ctor_set(v___x_1411_, 1, v___y_1408_);
lean_ctor_set(v___x_1411_, 2, v___x_1409_);
v___y_1398_ = v___x_1411_;
goto v___jp_1397_;
}
else
{
lean_object* v___x_1412_; 
lean_dec(v___x_1409_);
lean_inc(v_stopPos_1394_);
lean_inc_ref(v_str_1392_);
v___x_1412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1412_, 0, v_str_1392_);
lean_ctor_set(v___x_1412_, 1, v___y_1408_);
lean_ctor_set(v___x_1412_, 2, v_stopPos_1394_);
v___y_1398_ = v___x_1412_;
goto v___jp_1397_;
}
}
}
else
{
v___y_1377_ = v_rawComps_1372_;
goto v___jp_1376_;
}
v___jp_1376_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1378_ = l_List_lengthTR___redArg(v_nameComps_1375_);
v___x_1379_ = l_List_lengthTR___redArg(v___y_1377_);
v___x_1380_ = lean_nat_dec_eq(v___x_1378_, v___x_1379_);
lean_dec(v___x_1379_);
lean_dec(v___x_1378_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_dec(v___y_1377_);
lean_dec(v_nameComps_1375_);
lean_dec_ref(v_trailing_1371_);
lean_dec(v_pos_1370_);
lean_dec_ref(v_leading_1369_);
lean_dec_ref(v_rawVal_1367_);
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_comps_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_seps_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc(v___y_1377_);
v___x_1382_ = l_List_zipWith___at___00List_zip_spec__0(lean_box(0), lean_box(0), v_nameComps_1375_, v___y_1377_);
v___x_1383_ = lean_box(0);
v_comps_1384_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1367_, v_pos_1370_, v_trailing_1371_, v_leading_1369_, v___x_1382_, v___x_1383_);
v___x_1385_ = lean_array_mk(v___y_1377_);
v___x_1386_ = lean_array_pop(v___x_1385_);
v___x_1387_ = lean_array_to_list(v___x_1386_);
v_seps_1388_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1367_, v_pos_1370_, v___x_1387_, v___x_1383_);
lean_dec(v_pos_1370_);
lean_dec_ref(v_rawVal_1367_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_comps_1384_);
lean_ctor_set(v___x_1389_, 1, v_seps_1388_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
else
{
lean_object* v___x_1416_; 
lean_dec(v_rawComps_1372_);
lean_dec_ref(v_trailing_1371_);
lean_dec(v_pos_1370_);
lean_dec_ref(v_leading_1369_);
lean_dec(v_val_1368_);
lean_dec_ref(v_rawVal_1367_);
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
}
else
{
lean_object* v___x_1417_; 
lean_dec_ref_known(v_stx_1364_, 4);
lean_dec(v_info_1366_);
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_dec(v_stx_1364_);
v___x_1418_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__5, &l_Lean_Syntax_identComponents_x3f___closed__5_once, _init_l_Lean_Syntax_identComponents_x3f___closed__5);
v___x_1419_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___boxed(lean_object* v_stx_1420_, lean_object* v_nFields_x3f_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Syntax_identComponents_x3f(v_stx_1420_, v_nFields_x3f_1421_);
lean_dec(v_nFields_x3f_1421_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1423_, lean_object* v_nFields_x3f_1424_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1424_) == 1)
{
lean_object* v_val_1425_; lean_object* v_nameComps_1426_; lean_object* v___x_1427_; lean_object* v_nPrefix_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_namePrefix_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v_val_1425_ = lean_ctor_get(v_nFields_x3f_1424_, 0);
v_nameComps_1426_ = l_Lean_Name_components(v_n_1423_);
v___x_1427_ = l_List_lengthTR___redArg(v_nameComps_1426_);
v_nPrefix_1428_ = lean_nat_sub(v___x_1427_, v_val_1425_);
lean_dec(v___x_1427_);
v___x_1429_ = lean_box(0);
v___x_1430_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps___closed__0));
lean_inc(v_nPrefix_1428_);
lean_inc(v_nameComps_1426_);
v___x_1431_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_nameComps_1426_, v_nameComps_1426_, v_nPrefix_1428_, v___x_1430_);
v_namePrefix_1432_ = l_List_foldl___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(v___x_1429_, v___x_1431_);
v___x_1433_ = l_List_drop___redArg(v_nPrefix_1428_, v_nameComps_1426_);
lean_dec(v_nameComps_1426_);
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_namePrefix_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Name_components(v_n_1423_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps___boxed(lean_object* v_n_1436_, lean_object* v_nFields_x3f_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_n_1436_, v_nFields_x3f_1437_);
lean_dec(v_nFields_x3f_1437_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1439_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_panic_fn_borrowed(v___x_1440_, v_msg_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
if (lean_obj_tag(v_a_1443_) == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_info_1442_);
v___x_1445_ = l_List_reverse___redArg(v_a_1444_);
return v___x_1445_;
}
else
{
lean_object* v_head_1446_; lean_object* v_tail_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1462_; 
v_head_1446_ = lean_ctor_get(v_a_1443_, 0);
v_tail_1447_ = lean_ctor_get(v_a_1443_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_a_1443_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1449_ = v_a_1443_;
v_isShared_1450_ = v_isSharedCheck_1462_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_tail_1447_);
lean_inc(v_head_1446_);
lean_dec(v_a_1443_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1462_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1451_ = 1;
lean_inc(v_head_1446_);
v___x_1452_ = l_Lean_Name_toString(v_head_1446_, v___x_1451_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_string_utf8_byte_size(v___x_1452_);
v___x_1455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1452_);
lean_ctor_set(v___x_1455_, 1, v___x_1453_);
lean_ctor_set(v___x_1455_, 2, v___x_1454_);
v___x_1456_ = lean_box(0);
lean_inc(v_info_1442_);
v___x_1457_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1457_, 0, v_info_1442_);
lean_ctor_set(v___x_1457_, 1, v___x_1455_);
lean_ctor_set(v___x_1457_, 2, v_head_1446_);
lean_ctor_set(v___x_1457_, 3, v___x_1456_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 1, v_a_1444_);
lean_ctor_set(v___x_1449_, 0, v___x_1457_);
v___x_1459_ = v___x_1449_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1444_);
v___x_1459_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
v_a_1443_ = v_tail_1447_;
v_a_1444_ = v___x_1459_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1464_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1465_ = lean_unsigned_to_nat(9u);
v___x_1466_ = lean_unsigned_to_nat(377u);
v___x_1467_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1468_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
v___x_1469_ = l_mkPanicMessageWithDecl(v___x_1468_, v___x_1467_, v___x_1466_, v___x_1465_, v___x_1464_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1470_, lean_object* v_nFields_x3f_1471_){
_start:
{
if (lean_obj_tag(v_stx_1470_) == 3)
{
lean_object* v_info_1472_; lean_object* v_rawVal_1473_; lean_object* v_val_1474_; lean_object* v_val_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_info_1472_ = lean_ctor_get(v_stx_1470_, 0);
lean_inc(v_info_1472_);
v_rawVal_1473_ = lean_ctor_get(v_stx_1470_, 1);
v_val_1474_ = lean_ctor_get(v_stx_1470_, 2);
v_val_1475_ = l_Lean_Name_eraseMacroScopes(v_val_1474_);
v___x_1476_ = l_Lean_Name_getNumParts(v_val_1475_);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_dec_le(v___x_1476_, v___x_1477_);
lean_dec(v___x_1476_);
if (v___x_1478_ == 0)
{
if (lean_obj_tag(v_info_1472_) == 0)
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Syntax_identComponents_x3f(v_stx_1470_, v_nFields_x3f_1471_);
if (lean_obj_tag(v___x_1479_) == 1)
{
lean_object* v_val_1480_; lean_object* v_fst_1481_; 
lean_dec_ref_known(v_info_1472_, 4);
lean_dec(v_val_1475_);
v_val_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v___x_1479_, 1);
v_fst_1481_ = lean_ctor_get(v_val_1480_, 0);
lean_inc(v_fst_1481_);
lean_dec(v_val_1480_);
return v_fst_1481_;
}
else
{
lean_object* v_nameComps_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v___x_1479_);
v_nameComps_1482_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1475_, v_nFields_x3f_1471_);
v___x_1483_ = lean_box(0);
v___x_1484_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1472_, v_nameComps_1482_, v___x_1483_);
return v___x_1484_;
}
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref_known(v_stx_1470_, 4);
v___x_1485_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1475_, v_nFields_x3f_1471_);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1472_, v___x_1485_, v___x_1486_);
return v___x_1487_;
}
}
else
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1496_; 
lean_inc_ref(v_rawVal_1473_);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_stx_1470_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; 
v_unused_1497_ = lean_ctor_get(v_stx_1470_, 3);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_stx_1470_, 2);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_stx_1470_, 1);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_stx_1470_, 0);
lean_dec(v_unused_1500_);
v___x_1489_ = v_stx_1470_;
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_stx_1470_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_box(0);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 3, v___x_1491_);
lean_ctor_set(v___x_1489_, 2, v_val_1475_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_info_1472_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_rawVal_1473_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_val_1475_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
lean_ctor_set(v___x_1494_, 1, v___x_1491_);
return v___x_1494_;
}
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v_stx_1470_);
v___x_1501_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1502_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1501_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents___boxed(lean_object* v_stx_1503_, lean_object* v_nFields_x3f_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Syntax_identComponents(v_stx_1503_, v_nFields_x3f_1504_);
lean_dec(v_nFields_x3f_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1506_, uint8_t v_firstChoiceOnly_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1508_, 0, v_stx_1506_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*1, v_firstChoiceOnly_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1509_, lean_object* v_firstChoiceOnly_1510_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1511_; lean_object* v_res_1512_; 
v_firstChoiceOnly_boxed_1511_ = lean_unbox(v_firstChoiceOnly_1510_);
v_res_1512_ = l_Lean_Syntax_topDown(v_stx_1509_, v_firstChoiceOnly_boxed_1511_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1513_, lean_object* v_____r_1514_, lean_object* v_b_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_b_1515_);
v___x_1517_ = lean_apply_2(v_toPure_1513_, lean_box(0), v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1518_, lean_object* v_toPure_1519_, lean_object* v_____s_1520_){
_start:
{
lean_object* v_fst_1521_; 
v_fst_1521_ = lean_ctor_get(v_____s_1520_, 0);
if (lean_obj_tag(v_fst_1521_) == 0)
{
lean_object* v_snd_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_toPure_1519_);
v_snd_1522_ = lean_ctor_get(v_____s_1520_, 1);
lean_inc(v_snd_1522_);
lean_dec_ref(v_____s_1520_);
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_apply_2(v___f_1518_, v___x_1523_, v_snd_1522_);
return v___x_1524_;
}
else
{
lean_object* v_val_1525_; lean_object* v___x_1526_; 
lean_inc_ref(v_fst_1521_);
lean_dec_ref(v_____s_1520_);
lean_dec(v___f_1518_);
v_val_1525_ = lean_ctor_get(v_fst_1521_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v_fst_1521_, 1);
v___x_1526_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_val_1525_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1527_, lean_object* v_toPure_1528_, lean_object* v___x_1529_, lean_object* v_____do__lift_1530_){
_start:
{
if (lean_obj_tag(v_____do__lift_1530_) == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_dec(v___x_1529_);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v_____do__lift_1530_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v_snd_1527_);
v___x_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
v___x_1534_ = lean_apply_2(v_toPure_1528_, lean_box(0), v___x_1533_);
return v___x_1534_;
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v_snd_1527_);
v_a_1535_ = lean_ctor_get(v_____do__lift_1530_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_____do__lift_1530_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1537_ = v_____do__lift_1530_;
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v_____do__lift_1530_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1529_);
lean_ctor_set(v___x_1539_, 1, v_a_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1539_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_apply_2(v_toPure_1528_, lean_box(0), v___x_1541_);
return v___x_1542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1545_, lean_object* v___x_1546_, lean_object* v_inst_1547_, lean_object* v_f_1548_, lean_object* v_firstChoiceOnly_1549_, lean_object* v_toBind_1550_, lean_object* v_a_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1554_; lean_object* v_res_1555_; 
v_firstChoiceOnly_boxed_1554_ = lean_unbox(v_firstChoiceOnly_1549_);
v_res_1555_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1545_, v___x_1546_, v_inst_1547_, v_f_1548_, v_firstChoiceOnly_boxed_1554_, v_toBind_1550_, v_a_1551_, v_x_1552_, v___y_1553_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1559_, lean_object* v_stx_1560_, lean_object* v_inst_1561_, lean_object* v_f_1562_, uint8_t v_firstChoiceOnly_1563_, lean_object* v_toBind_1564_, lean_object* v___f_1565_, lean_object* v___x_1566_, lean_object* v___f_1567_, lean_object* v_____do__lift_1568_){
_start:
{
if (lean_obj_tag(v_____do__lift_1568_) == 0)
{
lean_object* v___x_1569_; 
lean_dec(v___f_1567_);
lean_dec(v___f_1565_);
lean_dec(v_toBind_1564_);
lean_dec(v_f_1562_);
lean_dec_ref(v_inst_1561_);
lean_dec(v_stx_1560_);
v___x_1569_ = lean_apply_2(v_toPure_1559_, lean_box(0), v_____do__lift_1568_);
return v___x_1569_;
}
else
{
if (lean_obj_tag(v_stx_1560_) == 1)
{
lean_object* v_a_1570_; lean_object* v_kind_1571_; lean_object* v_args_1572_; 
lean_dec(v___f_1567_);
v_a_1570_ = lean_ctor_get(v_____do__lift_1568_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v_____do__lift_1568_, 1);
v_kind_1571_ = lean_ctor_get(v_stx_1560_, 1);
lean_inc(v_kind_1571_);
v_args_1572_ = lean_ctor_get(v_stx_1560_, 2);
lean_inc_ref(v_args_1572_);
lean_dec_ref_known(v_stx_1560_, 3);
if (v_firstChoiceOnly_1563_ == 0)
{
lean_dec(v_kind_1571_);
goto v___jp_1573_;
}
else
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1583_ = lean_name_eq(v_kind_1571_, v___x_1582_);
lean_dec(v_kind_1571_);
if (v___x_1583_ == 0)
{
goto v___jp_1573_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec(v___f_1565_);
lean_dec(v_toBind_1564_);
lean_dec(v_toPure_1559_);
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = lean_array_get(v___x_1566_, v_args_1572_, v___x_1584_);
lean_dec_ref(v_args_1572_);
v___x_1586_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1561_, v_f_1562_, v_firstChoiceOnly_1563_, v___x_1585_, v_a_1570_);
return v___x_1586_;
}
}
v___jp_1573_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; size_t v_sz_1578_; size_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = lean_box(v_firstChoiceOnly_1563_);
lean_inc(v_toBind_1564_);
lean_inc_ref(v_inst_1561_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1576_, 0, v_toPure_1559_);
lean_closure_set(v___f_1576_, 1, v___x_1574_);
lean_closure_set(v___f_1576_, 2, v_inst_1561_);
lean_closure_set(v___f_1576_, 3, v_f_1562_);
lean_closure_set(v___f_1576_, 4, v___x_1575_);
lean_closure_set(v___f_1576_, 5, v_toBind_1564_);
v___x_1577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1574_);
lean_ctor_set(v___x_1577_, 1, v_a_1570_);
v_sz_1578_ = lean_array_size(v_args_1572_);
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1561_, v_args_1572_, v___f_1576_, v_sz_1578_, v___x_1579_, v___x_1577_);
v___x_1581_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v___x_1580_, v___f_1565_);
return v___x_1581_;
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec(v___f_1565_);
lean_dec(v_toBind_1564_);
lean_dec(v_f_1562_);
lean_dec_ref(v_inst_1561_);
lean_dec(v_stx_1560_);
lean_dec(v_toPure_1559_);
v_a_1587_ = lean_ctor_get(v_____do__lift_1568_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v_____do__lift_1568_, 1);
v___x_1588_ = lean_box(0);
v___x_1589_ = lean_apply_2(v___f_1567_, v___x_1588_, v_a_1587_);
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1590_, lean_object* v_stx_1591_, lean_object* v_inst_1592_, lean_object* v_f_1593_, lean_object* v_firstChoiceOnly_1594_, lean_object* v_toBind_1595_, lean_object* v___f_1596_, lean_object* v___x_1597_, lean_object* v___f_1598_, lean_object* v_____do__lift_1599_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1600_; lean_object* v_res_1601_; 
v_firstChoiceOnly_boxed_1600_ = lean_unbox(v_firstChoiceOnly_1594_);
v_res_1601_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1590_, v_stx_1591_, v_inst_1592_, v_f_1593_, v_firstChoiceOnly_boxed_1600_, v_toBind_1595_, v___f_1596_, v___x_1597_, v___f_1598_, v_____do__lift_1599_);
lean_dec(v___x_1597_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1602_, lean_object* v_f_1603_, uint8_t v_firstChoiceOnly_1604_, lean_object* v_stx_1605_, lean_object* v_b_1606_){
_start:
{
lean_object* v_toApplicative_1607_; lean_object* v_toBind_1608_; lean_object* v_toPure_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; lean_object* v___f_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
v_toApplicative_1607_ = lean_ctor_get(v_inst_1602_, 0);
v_toBind_1608_ = lean_ctor_get(v_inst_1602_, 1);
lean_inc_n(v_toBind_1608_, 2);
v_toPure_1609_ = lean_ctor_get(v_toApplicative_1607_, 1);
lean_inc_n(v_toPure_1609_, 3);
v___x_1610_ = lean_box(0);
lean_inc(v_f_1603_);
lean_inc(v_stx_1605_);
v___x_1611_ = lean_apply_2(v_f_1603_, v_stx_1605_, v_b_1606_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1612_, 0, v_toPure_1609_);
lean_inc_ref(v___f_1612_);
v___f_1613_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1613_, 0, v___f_1612_);
lean_closure_set(v___f_1613_, 1, v_toPure_1609_);
v___x_1614_ = lean_box(v_firstChoiceOnly_1604_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1615_, 0, v_toPure_1609_);
lean_closure_set(v___f_1615_, 1, v_stx_1605_);
lean_closure_set(v___f_1615_, 2, v_inst_1602_);
lean_closure_set(v___f_1615_, 3, v_f_1603_);
lean_closure_set(v___f_1615_, 4, v___x_1614_);
lean_closure_set(v___f_1615_, 5, v_toBind_1608_);
lean_closure_set(v___f_1615_, 6, v___f_1613_);
lean_closure_set(v___f_1615_, 7, v___x_1610_);
lean_closure_set(v___f_1615_, 8, v___f_1612_);
v___x_1616_ = lean_apply_4(v_toBind_1608_, lean_box(0), lean_box(0), v___x_1611_, v___f_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1617_, lean_object* v___x_1618_, lean_object* v_inst_1619_, lean_object* v_f_1620_, uint8_t v_firstChoiceOnly_1621_, lean_object* v_toBind_1622_, lean_object* v_a_1623_, lean_object* v_x_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_snd_1626_; lean_object* v___f_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_snd_1626_ = lean_ctor_get(v___y_1625_, 1);
lean_inc_n(v_snd_1626_, 2);
lean_dec_ref(v___y_1625_);
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1627_, 0, v_snd_1626_);
lean_closure_set(v___f_1627_, 1, v_toPure_1617_);
lean_closure_set(v___f_1627_, 2, v___x_1618_);
v___x_1628_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1619_, v_f_1620_, v_firstChoiceOnly_1621_, v_a_1623_, v_snd_1626_);
v___x_1629_ = lean_apply_4(v_toBind_1622_, lean_box(0), lean_box(0), v___x_1628_, v___f_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1630_, lean_object* v_f_1631_, lean_object* v_firstChoiceOnly_1632_, lean_object* v_stx_1633_, lean_object* v_b_1634_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1635_; lean_object* v_res_1636_; 
v_firstChoiceOnly_boxed_1635_ = lean_unbox(v_firstChoiceOnly_1632_);
v_res_1636_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1630_, v_f_1631_, v_firstChoiceOnly_boxed_1635_, v_stx_1633_, v_b_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1637_, lean_object* v_inst_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_f_1640_, uint8_t v_firstChoiceOnly_1641_, lean_object* v_stx_1642_, lean_object* v_b_1643_, lean_object* v_inst_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1638_, v_f_1640_, v_firstChoiceOnly_1641_, v_stx_1642_, v_b_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1646_, lean_object* v_inst_1647_, lean_object* v_00_u03b2_1648_, lean_object* v_f_1649_, lean_object* v_firstChoiceOnly_1650_, lean_object* v_stx_1651_, lean_object* v_b_1652_, lean_object* v_inst_1653_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1654_; lean_object* v_res_1655_; 
v_firstChoiceOnly_boxed_1654_ = lean_unbox(v_firstChoiceOnly_1650_);
v_res_1655_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1646_, v_inst_1647_, v_00_u03b2_1648_, v_f_1649_, v_firstChoiceOnly_boxed_1654_, v_stx_1651_, v_b_1652_, v_inst_1653_);
lean_dec(v_inst_1653_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1656_, lean_object* v_____do__lift_1657_){
_start:
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v_____do__lift_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref(v_____do__lift_1657_);
v___x_1659_ = lean_apply_2(v_toPure_1656_, lean_box(0), v_a_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1660_, lean_object* v_toBind_1661_, lean_object* v___f_1662_, lean_object* v_00_u03b2_1663_, lean_object* v_x_1664_, lean_object* v_init_1665_, lean_object* v_f_1666_){
_start:
{
uint8_t v_firstChoiceOnly_1667_; lean_object* v_stx_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_firstChoiceOnly_1667_ = lean_ctor_get_uint8(v_x_1664_, sizeof(void*)*1);
v_stx_1668_ = lean_ctor_get(v_x_1664_, 0);
lean_inc(v_stx_1668_);
lean_dec_ref(v_x_1664_);
v___x_1669_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1660_, v_f_1666_, v_firstChoiceOnly_1667_, v_stx_1668_, v_init_1665_);
v___x_1670_ = lean_apply_4(v_toBind_1661_, lean_box(0), lean_box(0), v___x_1669_, v___f_1662_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1671_){
_start:
{
lean_object* v_toApplicative_1672_; lean_object* v_toBind_1673_; lean_object* v_toPure_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; 
v_toApplicative_1672_ = lean_ctor_get(v_inst_1671_, 0);
v_toBind_1673_ = lean_ctor_get(v_inst_1671_, 1);
lean_inc(v_toBind_1673_);
v_toPure_1674_ = lean_ctor_get(v_toApplicative_1672_, 1);
lean_inc(v_toPure_1674_);
v___f_1675_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1675_, 0, v_toPure_1674_);
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1676_, 0, v_inst_1671_);
lean_closure_set(v___f_1676_, 1, v_toBind_1673_);
lean_closure_set(v___f_1676_, 2, v___f_1675_);
return v___f_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1677_, lean_object* v_inst_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1681_, lean_object* v_val_1682_){
_start:
{
if (lean_obj_tag(v_info_1681_) == 0)
{
lean_object* v_leading_1683_; lean_object* v_trailing_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_leading_1683_ = lean_ctor_get(v_info_1681_, 0);
lean_inc_ref(v_leading_1683_);
v_trailing_1684_ = lean_ctor_get(v_info_1681_, 2);
lean_inc_ref(v_trailing_1684_);
lean_dec_ref_known(v_info_1681_, 4);
v___x_1685_ = lean_substring_tostring(v_leading_1683_);
v___x_1686_ = lean_string_append(v___x_1685_, v_val_1682_);
v___x_1687_ = lean_substring_tostring(v_trailing_1684_);
v___x_1688_ = lean_string_append(v___x_1686_, v___x_1687_);
lean_dec_ref(v___x_1687_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_info_1681_);
v___x_1689_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1690_ = lean_string_append(v___x_1689_, v_val_1682_);
v___x_1691_ = lean_string_append(v___x_1690_, v___x_1689_);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1692_, lean_object* v_val_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1692_, v_val_1693_);
lean_dec_ref(v_val_1693_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1695_, lean_object* v_as_1696_, size_t v_sz_1697_, size_t v_i_1698_, lean_object* v_b_1699_){
_start:
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_usize_dec_lt(v_i_1698_, v_sz_1697_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_b_1699_);
return v___x_1701_;
}
else
{
lean_object* v_snd_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1729_; 
v_snd_1702_ = lean_ctor_get(v_b_1699_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_b_1699_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v_b_1699_, 0);
lean_dec(v_unused_1730_);
v___x_1704_ = v_b_1699_;
v_isShared_1705_ = v_isSharedCheck_1729_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snd_1702_);
lean_dec(v_b_1699_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1729_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_array_uget_borrowed(v_as_1696_, v_i_1698_);
lean_inc(v_snd_1702_);
lean_inc(v_a_1706_);
v___x_1707_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1695_, v_a_1706_, v_snd_1702_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1708_; 
lean_del_object(v___x_1704_);
lean_dec(v_snd_1702_);
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
else
{
lean_object* v_val_1709_; 
v_val_1709_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_val_1709_);
if (lean_obj_tag(v_val_1709_) == 0)
{
lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1719_; 
v_isSharedCheck_1719_ = !lean_is_exclusive(v_val_1709_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; 
v_unused_1720_ = lean_ctor_get(v_val_1709_, 0);
lean_dec(v_unused_1720_);
v___x_1711_ = v_val_1709_;
v_isShared_1712_ = v_isSharedCheck_1719_;
goto v_resetjp_1710_;
}
else
{
lean_dec(v_val_1709_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1719_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1707_);
v___x_1714_ = v___x_1704_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_snd_1702_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 1);
lean_ctor_set(v___x_1711_, 0, v___x_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
lean_dec_ref_known(v___x_1707_, 1);
lean_dec(v_snd_1702_);
v_a_1721_ = lean_ctor_get(v_val_1709_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v_val_1709_, 1);
v___x_1722_ = lean_box(0);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_a_1721_);
lean_ctor_set(v___x_1704_, 0, v___x_1722_);
v___x_1724_ = v___x_1704_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_a_1721_);
v___x_1724_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
size_t v___x_1725_; size_t v___x_1726_; 
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_i_1698_, v___x_1725_);
v_i_1698_ = v___x_1726_;
v_b_1699_ = v___x_1724_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1731_, lean_object* v_a_1732_, lean_object* v_b_1733_){
_start:
{
lean_object* v_array_1734_; lean_object* v_start_1735_; lean_object* v_stop_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1755_; 
v_array_1734_ = lean_ctor_get(v_a_1732_, 0);
v_start_1735_ = lean_ctor_get(v_a_1732_, 1);
v_stop_1736_ = lean_ctor_get(v_a_1732_, 2);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_a_1732_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1738_ = v_a_1732_;
v_isShared_1739_ = v_isSharedCheck_1755_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_stop_1736_);
lean_inc(v_start_1735_);
lean_inc(v_array_1734_);
lean_dec(v_a_1732_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1755_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_nat_dec_lt(v_start_1735_, v_stop_1736_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_del_object(v___x_1738_);
lean_dec(v_stop_1736_);
lean_dec(v_start_1735_);
lean_dec_ref(v_array_1734_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_b_1733_);
return v___x_1741_;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_array_fget_borrowed(v_array_1734_, v_start_1735_);
lean_inc(v___x_1742_);
v___x_1743_ = l_Lean_Syntax_reprint(v___x_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v___x_1744_; 
lean_del_object(v___x_1738_);
lean_dec(v_stop_1736_);
lean_dec(v_start_1735_);
lean_dec_ref(v_array_1734_);
v___x_1744_ = lean_box(0);
return v___x_1744_;
}
else
{
lean_object* v_val_1745_; uint8_t v___x_1746_; 
v_val_1745_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1746_ = lean_string_dec_eq(v_val_1731_, v_val_1745_);
lean_dec(v_val_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; 
lean_del_object(v___x_1738_);
lean_dec(v_stop_1736_);
lean_dec(v_start_1735_);
lean_dec_ref(v_array_1734_);
v___x_1747_ = lean_box(0);
return v___x_1747_;
}
else
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1748_ = lean_box(0);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_start_1735_, v___x_1749_);
lean_dec(v_start_1735_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v___x_1750_);
v___x_1752_ = v___x_1738_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_array_1734_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_stop_1736_);
v___x_1752_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
v_a_1732_ = v___x_1752_;
v_b_1733_ = v___x_1748_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1756_, lean_object* v_stx_1757_, lean_object* v_b_1758_){
_start:
{
lean_object* v_b_1760_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___x_1774_; lean_object* v_a_1776_; 
v___x_1774_ = lean_box(0);
switch(lean_obj_tag(v_stx_1757_))
{
case 2:
{
lean_object* v_info_1785_; lean_object* v_val_1786_; lean_object* v___x_1787_; lean_object* v_s_1788_; 
v_info_1785_ = lean_ctor_get(v_stx_1757_, 0);
v_val_1786_ = lean_ctor_get(v_stx_1757_, 1);
lean_inc(v_info_1785_);
v___x_1787_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1785_, v_val_1786_);
v_s_1788_ = lean_string_append(v_b_1758_, v___x_1787_);
lean_dec_ref(v___x_1787_);
v_a_1776_ = v_s_1788_;
goto v___jp_1775_;
}
case 3:
{
lean_object* v_rawVal_1789_; lean_object* v_info_1790_; lean_object* v_str_1791_; lean_object* v_startPos_1792_; lean_object* v_stopPos_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v_s_1796_; 
v_rawVal_1789_ = lean_ctor_get(v_stx_1757_, 1);
v_info_1790_ = lean_ctor_get(v_stx_1757_, 0);
v_str_1791_ = lean_ctor_get(v_rawVal_1789_, 0);
v_startPos_1792_ = lean_ctor_get(v_rawVal_1789_, 1);
v_stopPos_1793_ = lean_ctor_get(v_rawVal_1789_, 2);
v___x_1794_ = lean_string_utf8_extract(v_str_1791_, v_startPos_1792_, v_stopPos_1793_);
lean_inc(v_info_1790_);
v___x_1795_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1790_, v___x_1794_);
lean_dec_ref(v___x_1794_);
v_s_1796_ = lean_string_append(v_b_1758_, v___x_1795_);
lean_dec_ref(v___x_1795_);
v_a_1776_ = v_s_1796_;
goto v___jp_1775_;
}
case 1:
{
lean_object* v_kind_1797_; lean_object* v_args_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_kind_1797_ = lean_ctor_get(v_stx_1757_, 1);
v_args_1798_ = lean_ctor_get(v_stx_1757_, 2);
v___x_1799_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1800_ = lean_name_eq(v_kind_1797_, v___x_1799_);
if (v___x_1800_ == 0)
{
v_a_1776_ = v_b_1758_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_array_get_borrowed(v___x_1774_, v_args_1798_, v___x_1801_);
lean_inc(v___x_1802_);
v___x_1803_ = l_Lean_Syntax_reprint(v___x_1802_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v_stx_1757_, 3);
lean_dec_ref(v_b_1758_);
v___x_1804_ = lean_box(0);
return v___x_1804_;
}
else
{
lean_object* v_val_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_val_1805_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_array_get_size(v_args_1798_);
lean_inc_ref(v_args_1798_);
v___x_1808_ = l_Array_toSubarray___redArg(v_args_1798_, v___x_1806_, v___x_1807_);
v___x_1809_ = lean_box(0);
v___x_1810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1805_, v___x_1808_, v___x_1809_);
lean_dec(v_val_1805_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref_known(v_stx_1757_, 3);
lean_dec_ref(v_b_1758_);
v___x_1811_ = lean_box(0);
return v___x_1811_;
}
else
{
lean_dec_ref_known(v___x_1810_, 1);
v_a_1776_ = v_b_1758_;
goto v___jp_1775_;
}
}
}
}
default: 
{
v_a_1776_ = v_b_1758_;
goto v___jp_1775_;
}
}
v___jp_1759_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_b_1760_);
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
v___jp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; size_t v_sz_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___y_1764_);
v_sz_1768_ = lean_array_size(v___y_1765_);
v___x_1769_ = ((size_t)0ULL);
v___x_1770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1756_, v___y_1765_, v_sz_1768_, v___x_1769_, v___x_1767_);
lean_dec_ref(v___y_1765_);
if (lean_obj_tag(v___x_1770_) == 0)
{
return v___x_1766_;
}
else
{
lean_object* v_val_1771_; lean_object* v_fst_1772_; 
v_val_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_val_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v_fst_1772_ = lean_ctor_get(v_val_1771_, 0);
if (lean_obj_tag(v_fst_1772_) == 0)
{
lean_object* v_snd_1773_; 
v_snd_1773_ = lean_ctor_get(v_val_1771_, 1);
lean_inc(v_snd_1773_);
lean_dec(v_val_1771_);
v_b_1760_ = v_snd_1773_;
goto v___jp_1759_;
}
else
{
lean_inc_ref(v_fst_1772_);
lean_dec(v_val_1771_);
return v_fst_1772_;
}
}
}
v___jp_1775_:
{
if (lean_obj_tag(v_stx_1757_) == 1)
{
if (v_firstChoiceOnly_1756_ == 0)
{
lean_object* v_args_1777_; 
v_args_1777_ = lean_ctor_get(v_stx_1757_, 2);
lean_inc_ref(v_args_1777_);
lean_dec_ref_known(v_stx_1757_, 3);
v___y_1764_ = v_a_1776_;
v___y_1765_ = v_args_1777_;
goto v___jp_1763_;
}
else
{
lean_object* v_kind_1778_; lean_object* v_args_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v_kind_1778_ = lean_ctor_get(v_stx_1757_, 1);
lean_inc(v_kind_1778_);
v_args_1779_ = lean_ctor_get(v_stx_1757_, 2);
lean_inc_ref(v_args_1779_);
lean_dec_ref_known(v_stx_1757_, 3);
v___x_1780_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1781_ = lean_name_eq(v_kind_1778_, v___x_1780_);
lean_dec(v_kind_1778_);
if (v___x_1781_ == 0)
{
v___y_1764_ = v_a_1776_;
v___y_1765_ = v_args_1779_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_array_get(v___x_1774_, v_args_1779_, v___x_1782_);
lean_dec_ref(v_args_1779_);
v_stx_1757_ = v___x_1783_;
v_b_1758_ = v_a_1776_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1757_);
v_b_1760_ = v_a_1776_;
goto v___jp_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1812_){
_start:
{
lean_object* v_s_1813_; uint8_t v___x_1814_; lean_object* v___x_1815_; 
v_s_1813_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1814_ = 1;
v___x_1815_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1814_, v_stx_1812_, v_s_1813_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_box(0);
return v___x_1816_;
}
else
{
lean_object* v_val_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1825_; 
v_val_1817_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1819_ = v___x_1815_;
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_val_1817_);
lean_dec(v___x_1815_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1825_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_a_1821_; lean_object* v___x_1823_; 
v_a_1821_ = lean_ctor_get(v_val_1817_, 0);
lean_inc(v_a_1821_);
lean_dec(v_val_1817_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v_a_1821_);
v___x_1823_ = v___x_1819_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1826_, lean_object* v_a_1827_, lean_object* v_b_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1826_, v_a_1827_, v_b_1828_);
lean_dec_ref(v_val_1826_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1830_, lean_object* v_as_1831_, lean_object* v_sz_1832_, lean_object* v_i_1833_, lean_object* v_b_1834_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1835_; size_t v_sz_boxed_1836_; size_t v_i_boxed_1837_; lean_object* v_res_1838_; 
v_firstChoiceOnly_boxed_1835_ = lean_unbox(v_firstChoiceOnly_1830_);
v_sz_boxed_1836_ = lean_unbox_usize(v_sz_1832_);
lean_dec(v_sz_1832_);
v_i_boxed_1837_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_res_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1835_, v_as_1831_, v_sz_boxed_1836_, v_i_boxed_1837_, v_b_1834_);
lean_dec_ref(v_as_1831_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1839_, lean_object* v_stx_1840_, lean_object* v_b_1841_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1842_; lean_object* v_res_1843_; 
v_firstChoiceOnly_boxed_1842_ = lean_unbox(v_firstChoiceOnly_1839_);
v_res_1843_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1842_, v_stx_1840_, v_b_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1844_, lean_object* v_inst_1845_, lean_object* v_R_1846_, lean_object* v_a_1847_, lean_object* v_b_1848_, lean_object* v_c_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1844_, v_a_1847_, v_b_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1851_, lean_object* v_inst_1852_, lean_object* v_R_1853_, lean_object* v_a_1854_, lean_object* v_b_1855_, lean_object* v_c_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1851_, v_inst_1852_, v_R_1853_, v_a_1854_, v_b_1855_, v_c_1856_);
lean_dec_ref(v_val_1851_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1866_, lean_object* v_stx_1867_){
_start:
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_box(0);
v___x_1869_ = l_Lean_Syntax_isMissing(v_stx_1867_);
if (v___x_1869_ == 0)
{
if (lean_obj_tag(v_stx_1867_) == 1)
{
lean_object* v_kind_1870_; lean_object* v_args_1871_; 
v_kind_1870_ = lean_ctor_get(v_stx_1867_, 1);
v_args_1871_ = lean_ctor_get(v_stx_1867_, 2);
if (v_firstChoiceOnly_1866_ == 0)
{
goto v___jp_1872_;
}
else
{
lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1882_ = lean_name_eq(v_kind_1870_, v___x_1881_);
if (v___x_1882_ == 0)
{
goto v___jp_1872_;
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_unsigned_to_nat(0u);
v___x_1885_ = lean_array_get_borrowed(v___x_1883_, v_args_1871_, v___x_1884_);
v_stx_1867_ = v___x_1885_;
goto _start;
}
}
v___jp_1872_:
{
lean_object* v___x_1873_; size_t v_sz_1874_; size_t v___x_1875_; lean_object* v___x_1876_; lean_object* v_fst_1877_; 
v___x_1873_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1874_ = lean_array_size(v_args_1871_);
v___x_1875_ = ((size_t)0ULL);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1866_, v_args_1871_, v_sz_1874_, v___x_1875_, v___x_1873_);
v_fst_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_fst_1877_);
if (lean_obj_tag(v_fst_1877_) == 0)
{
lean_object* v_snd_1878_; lean_object* v___x_1879_; 
v_snd_1878_ = lean_ctor_get(v___x_1876_, 1);
lean_inc(v_snd_1878_);
lean_dec_ref(v___x_1876_);
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_snd_1878_);
return v___x_1879_;
}
else
{
lean_object* v_val_1880_; 
lean_dec_ref(v___x_1876_);
v_val_1880_ = lean_ctor_get(v_fst_1877_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v_fst_1877_, 1);
return v_val_1880_;
}
}
}
else
{
lean_object* v___x_1887_; 
v___x_1887_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_1887_;
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_box(v___x_1869_);
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1868_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_1892_, lean_object* v_as_1893_, size_t v_sz_1894_, size_t v_i_1895_, lean_object* v_b_1896_){
_start:
{
uint8_t v___x_1897_; 
v___x_1897_ = lean_usize_dec_lt(v_i_1895_, v_sz_1894_);
if (v___x_1897_ == 0)
{
return v_b_1896_;
}
else
{
lean_object* v_snd_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1916_; 
v_snd_1898_ = lean_ctor_get(v_b_1896_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_b_1896_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v_b_1896_, 0);
lean_dec(v_unused_1917_);
v___x_1900_ = v_b_1896_;
v_isShared_1901_ = v_isSharedCheck_1916_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_snd_1898_);
lean_dec(v_b_1896_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1916_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_a_1902_; lean_object* v___x_1903_; 
v_a_1902_ = lean_array_uget_borrowed(v_as_1893_, v_i_1895_);
v___x_1903_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1892_, v_a_1902_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1904_);
v___x_1906_ = v___x_1900_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_snd_1898_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec(v_snd_1898_);
v_a_1908_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1909_ = lean_box(0);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v_a_1908_);
lean_ctor_set(v___x_1900_, 0, v___x_1909_);
v___x_1911_ = v___x_1900_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_a_1908_);
v___x_1911_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
size_t v___x_1912_; size_t v___x_1913_; 
v___x_1912_ = ((size_t)1ULL);
v___x_1913_ = lean_usize_add(v_i_1895_, v___x_1912_);
v_i_1895_ = v___x_1913_;
v_b_1896_ = v___x_1911_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_1918_, lean_object* v_as_1919_, lean_object* v_sz_1920_, lean_object* v_i_1921_, lean_object* v_b_1922_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1923_; size_t v_sz_boxed_1924_; size_t v_i_boxed_1925_; lean_object* v_res_1926_; 
v_firstChoiceOnly_boxed_1923_ = lean_unbox(v_firstChoiceOnly_1918_);
v_sz_boxed_1924_ = lean_unbox_usize(v_sz_1920_);
lean_dec(v_sz_1920_);
v_i_boxed_1925_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_1923_, v_as_1919_, v_sz_boxed_1924_, v_i_boxed_1925_, v_b_1922_);
lean_dec_ref(v_as_1919_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_1927_, lean_object* v_stx_1928_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1929_; lean_object* v_res_1930_; 
v_firstChoiceOnly_boxed_1929_ = lean_unbox(v_firstChoiceOnly_1927_);
v_res_1930_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_1929_, v_stx_1928_);
lean_dec(v_stx_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_1931_){
_start:
{
uint8_t v___x_1932_; lean_object* v___y_1934_; lean_object* v___x_1938_; lean_object* v_a_1939_; 
v___x_1932_ = 0;
v___x_1938_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_1932_, v_stx_1931_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1938_);
v___y_1934_ = v_a_1939_;
goto v___jp_1933_;
v___jp_1933_:
{
lean_object* v_fst_1935_; 
v_fst_1935_ = lean_ctor_get(v___y_1934_, 0);
lean_inc(v_fst_1935_);
lean_dec_ref(v___y_1934_);
if (lean_obj_tag(v_fst_1935_) == 0)
{
return v___x_1932_;
}
else
{
lean_object* v_val_1936_; uint8_t v___x_1937_; 
v_val_1936_ = lean_ctor_get(v_fst_1935_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v_fst_1935_, 1);
v___x_1937_ = lean_unbox(v_val_1936_);
lean_dec(v_val_1936_);
return v___x_1937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_1940_){
_start:
{
uint8_t v_res_1941_; lean_object* v_r_1942_; 
v_res_1941_ = l_Lean_Syntax_hasMissing(v_stx_1940_);
lean_dec(v_stx_1940_);
v_r_1942_ = lean_box(v_res_1941_);
return v_r_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_1943_, lean_object* v_stx_1944_, lean_object* v_b_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_1943_, v_stx_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_1947_, lean_object* v_stx_1948_, lean_object* v_b_1949_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1950_; lean_object* v_res_1951_; 
v_firstChoiceOnly_boxed_1950_ = lean_unbox(v_firstChoiceOnly_1947_);
v_res_1951_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_1950_, v_stx_1948_, v_b_1949_);
lean_dec_ref(v_b_1949_);
lean_dec(v_stx_1948_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_1952_, uint8_t v_canonicalOnly_1953_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_Syntax_getPos_x3f(v_stx_1952_, v_canonicalOnly_1953_);
if (lean_obj_tag(v___x_1954_) == 1)
{
lean_object* v_val_1955_; lean_object* v___x_1956_; 
v_val_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1952_, v_canonicalOnly_1953_);
if (lean_obj_tag(v___x_1956_) == 1)
{
lean_object* v_val_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
v_val_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_val_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_val_1955_);
lean_ctor_set(v___x_1961_, 1, v_val_1957_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_object* v___x_1966_; 
lean_dec(v___x_1956_);
lean_dec(v_val_1955_);
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
}
else
{
lean_object* v___x_1967_; 
lean_dec(v___x_1954_);
v___x_1967_ = lean_box(0);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_1968_, lean_object* v_canonicalOnly_1969_){
_start:
{
uint8_t v_canonicalOnly_boxed_1970_; lean_object* v_res_1971_; 
v_canonicalOnly_boxed_1970_ = lean_unbox(v_canonicalOnly_1969_);
v_res_1971_ = l_Lean_Syntax_getRange_x3f(v_stx_1968_, v_canonicalOnly_boxed_1970_);
lean_dec(v_stx_1968_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_1972_, uint8_t v_canonicalOnly_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Syntax_getPos_x3f(v_stx_1972_, v_canonicalOnly_1973_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_box(0);
return v___x_1975_;
}
else
{
lean_object* v_val_1976_; lean_object* v___x_1977_; 
v_val_1976_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_val_1976_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1977_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_1972_, v_canonicalOnly_1973_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_val_1976_);
v___x_1978_ = lean_box(0);
return v___x_1978_;
}
else
{
lean_object* v_val_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1987_; 
v_val_1979_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1981_ = v___x_1977_;
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_val_1979_);
lean_dec(v___x_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1987_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_val_1976_);
lean_ctor_set(v___x_1983_, 1, v_val_1979_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1983_);
v___x_1985_ = v___x_1981_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_1988_, lean_object* v_canonicalOnly_1989_){
_start:
{
uint8_t v_canonicalOnly_boxed_1990_; lean_object* v_res_1991_; 
v_canonicalOnly_boxed_1990_ = lean_unbox(v_canonicalOnly_1989_);
v_res_1991_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1988_, v_canonicalOnly_boxed_1990_);
lean_dec(v_stx_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_1992_, uint8_t v_canonical_1993_){
_start:
{
lean_object* v_start_1994_; lean_object* v_stop_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2004_; 
v_start_1994_ = lean_ctor_get(v_range_1992_, 0);
v_stop_1995_ = lean_ctor_get(v_range_1992_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_range_1992_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1997_ = v_range_1992_;
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_stop_1995_);
lean_inc(v_start_1994_);
lean_dec(v_range_1992_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1999_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1999_, 0, v_start_1994_);
lean_ctor_set(v___x_1999_, 1, v_stop_1995_);
lean_ctor_set_uint8(v___x_1999_, sizeof(void*)*2, v_canonical_1993_);
v___x_2000_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_1998_ == 0)
{
lean_ctor_set_tag(v___x_1997_, 2);
lean_ctor_set(v___x_1997_, 1, v___x_2000_);
lean_ctor_set(v___x_1997_, 0, v___x_1999_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2005_, lean_object* v_canonical_2006_){
_start:
{
uint8_t v_canonical_boxed_2007_; lean_object* v_res_2008_; 
v_canonical_boxed_2007_ = lean_unbox(v_canonical_2006_);
v_res_2008_ = l_Lean_Syntax_ofRange(v_range_2005_, v_canonical_boxed_2007_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2013_, 0, v_stx_2011_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
lean_ctor_set(v___x_2013_, 2, v___x_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2014_, lean_object* v_stx_2015_){
_start:
{
lean_object* v_parents_2016_; lean_object* v_idxs_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
v_parents_2016_ = lean_ctor_get(v_t_2014_, 1);
v_idxs_2017_ = lean_ctor_get(v_t_2014_, 2);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_t_2014_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v_t_2014_, 0);
lean_dec(v_unused_2025_);
v___x_2019_ = v_t_2014_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_idxs_2017_);
lean_inc(v_parents_2016_);
lean_dec(v_t_2014_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v_stx_2015_);
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_stx_2015_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_parents_2016_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_idxs_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2026_, lean_object* v_idx_2027_){
_start:
{
lean_object* v_cur_2028_; lean_object* v_parents_2029_; lean_object* v_idxs_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2050_; 
v_cur_2028_ = lean_ctor_get(v_t_2026_, 0);
v_parents_2029_ = lean_ctor_get(v_t_2026_, 1);
v_idxs_2030_ = lean_ctor_get(v_t_2026_, 2);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_t_2026_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2032_ = v_t_2026_;
v_isShared_2033_ = v_isSharedCheck_2050_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_idxs_2030_);
lean_inc(v_parents_2029_);
lean_inc(v_cur_2028_);
lean_dec(v_t_2026_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2050_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2034_ = l_Lean_Syntax_getNumArgs(v_cur_2028_);
v___x_2035_ = lean_nat_dec_lt(v_idx_2027_, v___x_2034_);
lean_dec(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2036_ = lean_box(0);
v___x_2037_ = lean_array_push(v_parents_2029_, v_cur_2028_);
v___x_2038_ = lean_array_push(v_idxs_2030_, v_idx_2027_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 2, v___x_2038_);
lean_ctor_set(v___x_2032_, 1, v___x_2037_);
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2040_ = v___x_2032_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2042_ = l_Lean_Syntax_getArg(v_cur_2028_, v_idx_2027_);
v___x_2043_ = lean_box(0);
v___x_2044_ = l_Lean_Syntax_setArg(v_cur_2028_, v_idx_2027_, v___x_2043_);
v___x_2045_ = lean_array_push(v_parents_2029_, v___x_2044_);
v___x_2046_ = lean_array_push(v_idxs_2030_, v_idx_2027_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 2, v___x_2046_);
lean_ctor_set(v___x_2032_, 1, v___x_2045_);
lean_ctor_set(v___x_2032_, 0, v___x_2042_);
v___x_2048_ = v___x_2032_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2051_){
_start:
{
lean_object* v_cur_2052_; lean_object* v_parents_2053_; lean_object* v_idxs_2054_; lean_object* v___y_2056_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_cur_2052_ = lean_ctor_get(v_t_2051_, 0);
v_parents_2053_ = lean_ctor_get(v_t_2051_, 1);
v_idxs_2054_ = lean_ctor_get(v_t_2051_, 2);
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_array_get_size(v_parents_2053_);
v___x_2062_ = lean_nat_dec_lt(v___x_2060_, v___x_2061_);
if (v___x_2062_ == 0)
{
return v_t_2051_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
lean_inc_ref(v_idxs_2054_);
lean_inc_ref(v_parents_2053_);
lean_inc(v_cur_2052_);
lean_dec_ref(v_t_2051_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_array_get_size(v_idxs_2054_);
v___x_2065_ = lean_unsigned_to_nat(1u);
v___x_2066_ = lean_nat_sub(v___x_2064_, v___x_2065_);
v___x_2067_ = lean_array_get_borrowed(v___x_2060_, v_idxs_2054_, v___x_2066_);
lean_dec(v___x_2066_);
v___x_2068_ = lean_nat_sub(v___x_2061_, v___x_2065_);
v___x_2069_ = lean_array_get_borrowed(v___x_2063_, v_parents_2053_, v___x_2068_);
lean_dec(v___x_2068_);
v___x_2070_ = l_Lean_Syntax_getNumArgs(v___x_2069_);
v___x_2071_ = lean_nat_dec_lt(v___x_2067_, v___x_2070_);
lean_dec(v___x_2070_);
if (v___x_2071_ == 0)
{
lean_dec(v_cur_2052_);
lean_inc(v___x_2069_);
v___y_2056_ = v___x_2069_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2072_; 
lean_inc(v___x_2069_);
v___x_2072_ = l_Lean_Syntax_setArg(v___x_2069_, v___x_2067_, v_cur_2052_);
v___y_2056_ = v___x_2072_;
goto v___jp_2055_;
}
}
v___jp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_array_pop(v_parents_2053_);
v___x_2058_ = lean_array_pop(v_idxs_2054_);
v___x_2059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2059_, 0, v___y_2056_);
lean_ctor_set(v___x_2059_, 1, v___x_2057_);
lean_ctor_set(v___x_2059_, 2, v___x_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2073_){
_start:
{
lean_object* v_parents_2074_; lean_object* v_idxs_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; 
v_parents_2074_ = lean_ctor_get(v_t_2073_, 1);
v_idxs_2075_ = lean_ctor_get(v_t_2073_, 2);
v___x_2076_ = lean_unsigned_to_nat(0u);
v___x_2077_ = lean_array_get_size(v_parents_2074_);
v___x_2078_ = lean_nat_dec_lt(v___x_2076_, v___x_2077_);
if (v___x_2078_ == 0)
{
return v_t_2073_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_inc_ref(v_idxs_2075_);
v___x_2079_ = l_Lean_Syntax_Traverser_up(v_t_2073_);
v___x_2080_ = lean_array_get_size(v_idxs_2075_);
v___x_2081_ = lean_unsigned_to_nat(1u);
v___x_2082_ = lean_nat_sub(v___x_2080_, v___x_2081_);
v___x_2083_ = lean_array_get(v___x_2076_, v_idxs_2075_, v___x_2082_);
lean_dec(v___x_2082_);
lean_dec_ref(v_idxs_2075_);
v___x_2084_ = lean_nat_sub(v___x_2083_, v___x_2081_);
lean_dec(v___x_2083_);
v___x_2085_ = l_Lean_Syntax_Traverser_down(v___x_2079_, v___x_2084_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2086_){
_start:
{
lean_object* v_parents_2087_; lean_object* v_idxs_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; uint8_t v___x_2091_; 
v_parents_2087_ = lean_ctor_get(v_t_2086_, 1);
v_idxs_2088_ = lean_ctor_get(v_t_2086_, 2);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_array_get_size(v_parents_2087_);
v___x_2091_ = lean_nat_dec_lt(v___x_2089_, v___x_2090_);
if (v___x_2091_ == 0)
{
return v_t_2086_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_inc_ref(v_idxs_2088_);
v___x_2092_ = l_Lean_Syntax_Traverser_up(v_t_2086_);
v___x_2093_ = lean_array_get_size(v_idxs_2088_);
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = lean_nat_sub(v___x_2093_, v___x_2094_);
v___x_2096_ = lean_array_get(v___x_2089_, v_idxs_2088_, v___x_2095_);
lean_dec(v___x_2095_);
lean_dec_ref(v_idxs_2088_);
v___x_2097_ = lean_nat_add(v___x_2096_, v___x_2094_);
lean_dec(v___x_2096_);
v___x_2098_ = l_Lean_Syntax_Traverser_down(v___x_2092_, v___x_2097_);
return v___x_2098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2099_){
_start:
{
lean_object* v_cur_2100_; 
v_cur_2100_ = lean_ctor_get(v_self_2099_, 0);
lean_inc(v_cur_2100_);
return v_cur_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2101_);
lean_dec_ref(v_self_2101_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2104_, lean_object* v_t_2105_){
_start:
{
lean_object* v_toApplicative_2106_; lean_object* v_toFunctor_2107_; lean_object* v_map_2108_; lean_object* v_get_2109_; lean_object* v___f_2110_; lean_object* v___x_2111_; 
v_toApplicative_2106_ = lean_ctor_get(v_inst_2104_, 0);
lean_inc_ref(v_toApplicative_2106_);
lean_dec_ref(v_inst_2104_);
v_toFunctor_2107_ = lean_ctor_get(v_toApplicative_2106_, 0);
lean_inc_ref(v_toFunctor_2107_);
lean_dec_ref(v_toApplicative_2106_);
v_map_2108_ = lean_ctor_get(v_toFunctor_2107_, 0);
lean_inc(v_map_2108_);
lean_dec_ref(v_toFunctor_2107_);
v_get_2109_ = lean_ctor_get(v_t_2105_, 0);
lean_inc(v_get_2109_);
lean_dec_ref(v_t_2105_);
v___f_2110_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2111_ = lean_apply_4(v_map_2108_, lean_box(0), lean_box(0), v___f_2110_, v_get_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2112_, lean_object* v_inst_2113_, lean_object* v_t_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2113_, v_t_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2116_, lean_object* v_s_2117_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_box(0);
v___x_2119_ = l_Lean_Syntax_Traverser_setCur(v_s_2117_, v_stx_2116_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2121_, lean_object* v_stx_2122_){
_start:
{
lean_object* v_modifyGet_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; 
v_modifyGet_2123_ = lean_ctor_get(v_t_2121_, 2);
lean_inc(v_modifyGet_2123_);
lean_dec_ref(v_t_2121_);
v___f_2124_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2124_, 0, v_stx_2122_);
v___x_2125_ = lean_apply_2(v_modifyGet_2123_, lean_box(0), v___f_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2126_, lean_object* v_t_2127_, lean_object* v_stx_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2127_, v_stx_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2130_, lean_object* v_s_2131_){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_box(0);
v___x_2133_ = l_Lean_Syntax_Traverser_down(v_s_2131_, v_idx_2130_);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2135_, lean_object* v_idx_2136_){
_start:
{
lean_object* v_modifyGet_2137_; lean_object* v___f_2138_; lean_object* v___x_2139_; 
v_modifyGet_2137_ = lean_ctor_get(v_t_2135_, 2);
lean_inc(v_modifyGet_2137_);
lean_dec_ref(v_t_2135_);
v___f_2138_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2138_, 0, v_idx_2136_);
v___x_2139_ = lean_apply_2(v_modifyGet_2137_, lean_box(0), v___f_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2140_, lean_object* v_t_2141_, lean_object* v_idx_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2141_, v_idx_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2144_){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = lean_box(0);
v___x_2146_ = l_Lean_Syntax_Traverser_up(v_s_2144_);
v___x_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2149_){
_start:
{
lean_object* v_modifyGet_2150_; lean_object* v___f_2151_; lean_object* v___x_2152_; 
v_modifyGet_2150_ = lean_ctor_get(v_t_2149_, 2);
lean_inc(v_modifyGet_2150_);
lean_dec_ref(v_t_2149_);
v___f_2151_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2152_ = lean_apply_2(v_modifyGet_2150_, lean_box(0), v___f_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2153_, lean_object* v_t_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2156_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = l_Lean_Syntax_Traverser_left(v_s_2156_);
v___x_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2161_){
_start:
{
lean_object* v_modifyGet_2162_; lean_object* v___f_2163_; lean_object* v___x_2164_; 
v_modifyGet_2162_ = lean_ctor_get(v_t_2161_, 2);
lean_inc(v_modifyGet_2162_);
lean_dec_ref(v_t_2161_);
v___f_2163_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2164_ = lean_apply_2(v_modifyGet_2162_, lean_box(0), v___f_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2165_, lean_object* v_t_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2168_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_box(0);
v___x_2170_ = l_Lean_Syntax_Traverser_right(v_s_2168_);
v___x_2171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2173_){
_start:
{
lean_object* v_modifyGet_2174_; lean_object* v___f_2175_; lean_object* v___x_2176_; 
v_modifyGet_2174_ = lean_ctor_get(v_t_2173_, 2);
lean_inc(v_modifyGet_2174_);
lean_dec_ref(v_t_2173_);
v___f_2175_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2176_ = lean_apply_2(v_modifyGet_2174_, lean_box(0), v___f_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2177_, lean_object* v_t_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2180_, lean_object* v_st_2181_){
_start:
{
lean_object* v_idxs_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_idxs_2182_ = lean_ctor_get(v_st_2181_, 2);
v___x_2183_ = lean_array_get_size(v_idxs_2182_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_sub(v___x_2183_, v___x_2184_);
v___x_2186_ = lean_nat_dec_lt(v___x_2185_, v___x_2183_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_dec(v___x_2185_);
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_apply_2(v_toPure_2180_, lean_box(0), v___x_2187_);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_array_fget_borrowed(v_idxs_2182_, v___x_2185_);
lean_dec(v___x_2185_);
lean_inc(v___x_2189_);
v___x_2190_ = lean_apply_2(v_toPure_2180_, lean_box(0), v___x_2189_);
return v___x_2190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2191_, lean_object* v_st_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2191_, v_st_2192_);
lean_dec_ref(v_st_2192_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2194_, lean_object* v_t_2195_){
_start:
{
lean_object* v_toApplicative_2196_; lean_object* v_toBind_2197_; lean_object* v_get_2198_; lean_object* v_toPure_2199_; lean_object* v___f_2200_; lean_object* v___x_2201_; 
v_toApplicative_2196_ = lean_ctor_get(v_inst_2194_, 0);
lean_inc_ref(v_toApplicative_2196_);
v_toBind_2197_ = lean_ctor_get(v_inst_2194_, 1);
lean_inc(v_toBind_2197_);
lean_dec_ref(v_inst_2194_);
v_get_2198_ = lean_ctor_get(v_t_2195_, 0);
lean_inc(v_get_2198_);
lean_dec_ref(v_t_2195_);
v_toPure_2199_ = lean_ctor_get(v_toApplicative_2196_, 1);
lean_inc(v_toPure_2199_);
lean_dec_ref(v_toApplicative_2196_);
v___f_2200_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2200_, 0, v_toPure_2199_);
v___x_2201_ = lean_apply_4(v_toBind_2197_, lean_box(0), lean_box(0), v_get_2198_, v___f_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2202_, lean_object* v_inst_2203_, lean_object* v_t_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2203_, v_t_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2206_, lean_object* v_i_2207_){
_start:
{
lean_object* v_args_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v_args_2208_ = lean_ctor_get(v_n_2206_, 2);
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_array_get_borrowed(v___x_2209_, v_args_2208_, v_i_2207_);
v___x_2211_ = l_Lean_Syntax_getId(v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2212_, lean_object* v_i_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_SyntaxNode_getIdAt(v_n_2212_, v_i_2213_);
lean_dec(v_i_2213_);
lean_dec(v_n_2212_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2215_){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2217_ = lean_box(2);
v___x_2218_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2216_);
lean_ctor_set(v___x_2218_, 2, v_args_2215_);
return v___x_2218_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 1)
{
lean_object* v_kind_2225_; 
v_kind_2225_ = lean_ctor_get(v_x_2224_, 1);
if (lean_obj_tag(v_kind_2225_) == 1)
{
lean_object* v_pre_2226_; lean_object* v_str_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v_pre_2226_ = lean_ctor_get(v_kind_2225_, 0);
v_str_2227_ = lean_ctor_get(v_kind_2225_, 1);
v___x_2228_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2229_ = lean_string_dec_eq(v_str_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2231_ = lean_string_dec_eq(v_str_2227_, v___x_2230_);
if (v___x_2231_ == 0)
{
return v___x_2231_;
}
else
{
if (lean_obj_tag(v_pre_2226_) == 1)
{
lean_object* v_pre_2232_; 
v_pre_2232_ = lean_ctor_get(v_pre_2226_, 0);
if (lean_obj_tag(v_pre_2232_) == 1)
{
lean_object* v_pre_2233_; 
v_pre_2233_ = lean_ctor_get(v_pre_2232_, 0);
if (lean_obj_tag(v_pre_2233_) == 1)
{
lean_object* v_pre_2234_; 
v_pre_2234_ = lean_ctor_get(v_pre_2233_, 0);
if (lean_obj_tag(v_pre_2234_) == 0)
{
lean_object* v_str_2235_; lean_object* v_str_2236_; lean_object* v_str_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_str_2235_ = lean_ctor_get(v_pre_2226_, 1);
v_str_2236_ = lean_ctor_get(v_pre_2232_, 1);
v_str_2237_ = lean_ctor_get(v_pre_2233_, 1);
v___x_2238_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2239_ = lean_string_dec_eq(v_str_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
return v___x_2229_;
}
else
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2241_ = lean_string_dec_eq(v_str_2236_, v___x_2240_);
if (v___x_2241_ == 0)
{
return v___x_2241_;
}
else
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2243_ = lean_string_dec_eq(v_str_2235_, v___x_2242_);
return v___x_2243_;
}
}
}
else
{
return v___x_2229_;
}
}
else
{
return v___x_2229_;
}
}
else
{
return v___x_2229_;
}
}
else
{
return v___x_2229_;
}
}
}
else
{
return v___x_2229_;
}
}
else
{
uint8_t v___x_2244_; 
v___x_2244_ = 0;
return v___x_2244_;
}
}
else
{
uint8_t v___x_2245_; 
v___x_2245_ = 0;
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2246_){
_start:
{
uint8_t v_res_2247_; lean_object* v_r_2248_; 
v_res_2247_ = l_Lean_Syntax_isQuot(v_x_2246_);
lean_dec(v_x_2246_);
v_r_2248_ = lean_box(v_res_2247_);
return v_r_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___y_2258_; uint8_t v___x_2264_; 
v___x_2255_ = l_Lean_Syntax_getNumArgs(v_stx_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_nat_dec_eq(v___x_2255_, v___x_2256_);
lean_dec(v___x_2255_);
if (v___x_2264_ == 0)
{
v___y_2258_ = v_stx_2254_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = l_Lean_Syntax_getArg(v_stx_2254_, v___x_2265_);
lean_dec(v_stx_2254_);
v___y_2258_ = v___x_2266_;
goto v___jp_2257_;
}
v___jp_2257_:
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2258_);
v___x_2260_ = l_Lean_Syntax_isOfKind(v___y_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Syntax_getArg(v___y_2258_, v___x_2256_);
lean_dec(v___y_2258_);
return v___x_2261_;
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_unsigned_to_nat(3u);
v___x_2263_ = l_Lean_Syntax_getArg(v___y_2258_, v___x_2262_);
lean_dec(v___y_2258_);
return v___x_2263_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2268_){
_start:
{
if (lean_obj_tag(v_x_2268_) == 1)
{
lean_object* v_kind_2269_; 
v_kind_2269_ = lean_ctor_get(v_x_2268_, 1);
if (lean_obj_tag(v_kind_2269_) == 1)
{
lean_object* v_str_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v_str_2270_ = lean_ctor_get(v_kind_2269_, 1);
v___x_2271_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2272_ = lean_string_dec_eq(v_str_2270_, v___x_2271_);
return v___x_2272_;
}
else
{
uint8_t v___x_2273_; 
v___x_2273_ = 0;
return v___x_2273_;
}
}
else
{
uint8_t v___x_2274_; 
v___x_2274_ = 0;
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2275_){
_start:
{
uint8_t v_res_2276_; lean_object* v_r_2277_; 
v_res_2276_ = l_Lean_Syntax_isAntiquot(v_x_2275_);
lean_dec(v_x_2275_);
v_r_2277_ = lean_box(v_res_2276_);
return v_r_2277_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(uint8_t v___y_2278_, uint8_t v___x_2279_, lean_object* v_as_2280_, size_t v_i_2281_, size_t v_stop_2282_){
_start:
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_usize_dec_eq(v_i_2281_, v_stop_2282_);
if (v___x_2283_ == 0)
{
uint8_t v___x_2284_; uint8_t v___y_2286_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2284_ = 1;
v___x_2290_ = lean_array_uget_borrowed(v_as_2280_, v_i_2281_);
v___x_2291_ = l_Lean_Syntax_isAntiquot(v___x_2290_);
if (v___x_2291_ == 0)
{
v___y_2286_ = v___y_2278_;
goto v___jp_2285_;
}
else
{
v___y_2286_ = v___x_2279_;
goto v___jp_2285_;
}
v___jp_2285_:
{
if (v___y_2286_ == 0)
{
size_t v___x_2287_; size_t v___x_2288_; 
v___x_2287_ = ((size_t)1ULL);
v___x_2288_ = lean_usize_add(v_i_2281_, v___x_2287_);
v_i_2281_ = v___x_2288_;
goto _start;
}
else
{
return v___x_2284_;
}
}
}
else
{
uint8_t v___x_2292_; 
v___x_2292_ = 0;
return v___x_2292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___y_2293_, lean_object* v___x_2294_, lean_object* v_as_2295_, lean_object* v_i_2296_, lean_object* v_stop_2297_){
_start:
{
uint8_t v___y_330__boxed_2298_; uint8_t v___x_331__boxed_2299_; size_t v_i_boxed_2300_; size_t v_stop_boxed_2301_; uint8_t v_res_2302_; lean_object* v_r_2303_; 
v___y_330__boxed_2298_ = lean_unbox(v___y_2293_);
v___x_331__boxed_2299_ = lean_unbox(v___x_2294_);
v_i_boxed_2300_ = lean_unbox_usize(v_i_2296_);
lean_dec(v_i_2296_);
v_stop_boxed_2301_ = lean_unbox_usize(v_stop_2297_);
lean_dec(v_stop_2297_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_330__boxed_2298_, v___x_331__boxed_2299_, v_as_2295_, v_i_boxed_2300_, v_stop_boxed_2301_);
lean_dec_ref(v_as_2295_);
v_r_2303_ = lean_box(v_res_2302_);
return v_r_2303_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2304_){
_start:
{
uint8_t v___x_2305_; uint8_t v___y_2307_; 
v___x_2305_ = l_Lean_Syntax_isAntiquot(v_stx_2304_);
if (v___x_2305_ == 0)
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2304_);
v___x_2316_ = l_Lean_Syntax_isOfKind(v_stx_2304_, v___x_2315_);
if (v___x_2316_ == 0)
{
v___y_2307_ = v___x_2316_;
goto v___jp_2306_;
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2317_ = lean_unsigned_to_nat(0u);
v___x_2318_ = l_Lean_Syntax_getNumArgs(v_stx_2304_);
v___x_2319_ = lean_nat_dec_lt(v___x_2317_, v___x_2318_);
lean_dec(v___x_2318_);
v___y_2307_ = v___x_2319_;
goto v___jp_2306_;
}
}
else
{
lean_dec(v_stx_2304_);
return v___x_2305_;
}
v___jp_2306_:
{
if (v___y_2307_ == 0)
{
lean_dec(v_stx_2304_);
return v___y_2307_;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2308_ = l_Lean_Syntax_getArgs(v_stx_2304_);
lean_dec(v_stx_2304_);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_array_get_size(v___x_2308_);
v___x_2311_ = lean_nat_dec_lt(v___x_2309_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v___x_2308_);
return v___y_2307_;
}
else
{
if (v___x_2311_ == 0)
{
lean_dec_ref(v___x_2308_);
return v___y_2307_;
}
else
{
size_t v___x_2312_; size_t v___x_2313_; uint8_t v___x_2314_; 
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = lean_usize_of_nat(v___x_2310_);
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___y_2307_, v___x_2305_, v___x_2308_, v___x_2312_, v___x_2313_);
lean_dec_ref(v___x_2308_);
if (v___x_2314_ == 0)
{
return v___x_2311_;
}
else
{
return v___x_2305_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2320_){
_start:
{
uint8_t v_res_2321_; lean_object* v_r_2322_; 
v_res_2321_ = l_Lean_Syntax_isAntiquots(v_stx_2320_);
v_r_2322_ = lean_box(v_res_2321_);
return v_r_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2323_){
_start:
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2323_);
v___x_2325_ = l_Lean_Syntax_isOfKind(v_stx_2323_, v___x_2324_);
if (v___x_2325_ == 0)
{
return v_stx_2323_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = l_Lean_Syntax_getArg(v_stx_2323_, v___x_2326_);
lean_dec(v_stx_2323_);
return v___x_2327_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2330_ = l_Lean_mkAtom(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2333_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2334_ = lean_unsigned_to_nat(4u);
v___x_2335_ = lean_mk_empty_array_with_capacity(v___x_2334_);
v___x_2336_ = lean_array_push(v___x_2335_, v___x_2333_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2345_ = l_Lean_mkAtom(v___x_2344_);
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2346_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2347_ = lean_unsigned_to_nat(2u);
v___x_2348_ = lean_mk_empty_array_with_capacity(v___x_2347_);
v___x_2349_ = lean_array_push(v___x_2348_, v___x_2346_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2361_ = l_Lean_mkAtom(v___x_2360_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2364_ = l_Lean_mkAtom(v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2365_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2366_ = lean_unsigned_to_nat(3u);
v___x_2367_ = lean_mk_empty_array_with_capacity(v___x_2366_);
v___x_2368_ = lean_array_push(v___x_2367_, v___x_2365_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2369_, lean_object* v_term_2370_, lean_object* v_nesting_2371_, lean_object* v_name_2372_, uint8_t v_isPseudoKind_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_nesting_2378_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2397_; uint8_t v___x_2405_; 
v___x_2374_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2375_ = lean_mk_array(v_nesting_2371_, v___x_2374_);
v___x_2376_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2377_ = lean_box(2);
v_nesting_2378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2378_, 0, v___x_2377_);
lean_ctor_set(v_nesting_2378_, 1, v___x_2376_);
lean_ctor_set(v_nesting_2378_, 2, v___x_2375_);
v___x_2405_ = l_Lean_Syntax_isIdent(v_term_2370_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2370_);
v___x_2407_ = l_Lean_Syntax_isOfKind(v_term_2370_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2408_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2409_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2410_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2411_ = lean_array_push(v___x_2410_, v_term_2370_);
v___x_2412_ = lean_array_push(v___x_2411_, v___x_2409_);
v___x_2413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2377_);
lean_ctor_set(v___x_2413_, 1, v___x_2408_);
lean_ctor_set(v___x_2413_, 2, v___x_2412_);
v___y_2397_ = v___x_2413_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = l_Lean_Syntax_getArg(v_term_2370_, v___x_2414_);
lean_dec(v_term_2370_);
v___y_2397_ = v___x_2415_;
goto v___jp_2396_;
}
}
else
{
v___y_2397_ = v_term_2370_;
goto v___jp_2396_;
}
v___jp_2379_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_inc(v___y_2382_);
v___x_2383_ = l_Lean_Name_append(v_kind_2369_, v___y_2382_);
v___x_2384_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2385_ = l_Lean_Name_append(v___x_2383_, v___x_2384_);
v___x_2386_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2387_ = lean_array_push(v___x_2386_, v_nesting_2378_);
v___x_2388_ = lean_array_push(v___x_2387_, v___y_2381_);
v___x_2389_ = lean_array_push(v___x_2388_, v___y_2380_);
v___x_2390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2377_);
lean_ctor_set(v___x_2390_, 1, v___x_2385_);
lean_ctor_set(v___x_2390_, 2, v___x_2389_);
return v___x_2390_;
}
v___jp_2391_:
{
if (v_isPseudoKind_2373_ == 0)
{
lean_object* v___x_2394_; 
v___x_2394_ = lean_box(0);
v___y_2380_ = v___y_2393_;
v___y_2381_ = v___y_2392_;
v___y_2382_ = v___x_2394_;
goto v___jp_2379_;
}
else
{
lean_object* v___x_2395_; 
v___x_2395_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2380_ = v___y_2393_;
v___y_2381_ = v___y_2392_;
v___y_2382_ = v___x_2395_;
goto v___jp_2379_;
}
}
v___jp_2396_:
{
if (lean_obj_tag(v_name_2372_) == 0)
{
lean_object* v___x_2398_; 
v___x_2398_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2392_ = v___y_2397_;
v___y_2393_ = v___x_2398_;
goto v___jp_2391_;
}
else
{
lean_object* v_val_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_val_2399_ = lean_ctor_get(v_name_2372_, 0);
lean_inc(v_val_2399_);
lean_dec_ref_known(v_name_2372_, 1);
v___x_2400_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2401_ = l_Lean_mkAtom(v_val_2399_);
v___x_2402_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2403_ = lean_array_push(v___x_2402_, v___x_2401_);
v___x_2404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2377_);
lean_ctor_set(v___x_2404_, 1, v___x_2400_);
lean_ctor_set(v___x_2404_, 2, v___x_2403_);
v___y_2392_ = v___y_2397_;
v___y_2393_ = v___x_2404_;
goto v___jp_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2416_, lean_object* v_term_2417_, lean_object* v_nesting_2418_, lean_object* v_name_2419_, lean_object* v_isPseudoKind_2420_){
_start:
{
uint8_t v_isPseudoKind_boxed_2421_; lean_object* v_res_2422_; 
v_isPseudoKind_boxed_2421_ = lean_unbox(v_isPseudoKind_2420_);
v_res_2422_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2416_, v_term_2417_, v_nesting_2418_, v_name_2419_, v_isPseudoKind_boxed_2421_);
return v_res_2422_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = l_Lean_Syntax_getArg(v_stx_2423_, v___x_2424_);
v___x_2426_ = l_Lean_Syntax_getArgs(v___x_2425_);
lean_dec(v___x_2425_);
v___x_2427_ = lean_array_get_size(v___x_2426_);
lean_dec_ref(v___x_2426_);
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = lean_nat_dec_eq(v___x_2427_, v___x_2428_);
if (v___x_2429_ == 0)
{
uint8_t v___x_2430_; 
v___x_2430_ = 1;
return v___x_2430_;
}
else
{
uint8_t v___x_2431_; 
v___x_2431_ = 0;
return v___x_2431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2432_){
_start:
{
uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_res_2433_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2432_);
lean_dec(v_stx_2432_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2435_){
_start:
{
uint8_t v___x_2436_; 
v___x_2436_ = l_Lean_Syntax_isAntiquot(v_stx_2435_);
if (v___x_2436_ == 0)
{
return v_stx_2435_;
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2438_ = l_Lean_Syntax_getArg(v_stx_2435_, v___x_2437_);
v___x_2439_ = l_Lean_Syntax_getArgs(v___x_2438_);
lean_dec(v___x_2438_);
v___x_2440_ = lean_array_pop(v___x_2439_);
v___x_2441_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2442_ = lean_box(2);
v___x_2443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v___x_2441_);
lean_ctor_set(v___x_2443_, 2, v___x_2440_);
v___x_2444_ = l_Lean_Syntax_setArg(v_stx_2435_, v___x_2437_, v___x_2443_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2445_){
_start:
{
lean_object* v___y_2447_; uint8_t v___x_2458_; 
v___x_2458_ = l_Lean_Syntax_isAntiquot(v_stx_2445_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_unsigned_to_nat(3u);
v___x_2460_ = l_Lean_Syntax_getArg(v_stx_2445_, v___x_2459_);
v___y_2447_ = v___x_2460_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_unsigned_to_nat(2u);
v___x_2462_ = l_Lean_Syntax_getArg(v_stx_2445_, v___x_2461_);
v___y_2447_ = v___x_2462_;
goto v___jp_2446_;
}
v___jp_2446_:
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Lean_Syntax_isIdent(v___y_2447_);
if (v___x_2448_ == 0)
{
uint8_t v___x_2449_; 
v___x_2449_ = l_Lean_Syntax_isAtom(v___y_2447_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_unsigned_to_nat(1u);
v___x_2451_ = l_Lean_Syntax_getArg(v___y_2447_, v___x_2450_);
lean_dec(v___y_2447_);
return v___x_2451_;
}
else
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2452_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = lean_mk_empty_array_with_capacity(v___x_2453_);
v___x_2455_ = lean_array_push(v___x_2454_, v___y_2447_);
v___x_2456_ = lean_box(2);
v___x_2457_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2452_);
lean_ctor_set(v___x_2457_, 2, v___x_2455_);
return v___x_2457_;
}
}
else
{
return v___y_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2463_);
lean_dec(v_stx_2463_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2465_){
_start:
{
if (lean_obj_tag(v_x_2465_) == 1)
{
lean_object* v_kind_2466_; 
v_kind_2466_ = lean_ctor_get(v_x_2465_, 1);
if (lean_obj_tag(v_kind_2466_) == 1)
{
lean_object* v_pre_2467_; lean_object* v_str_2468_; 
v_pre_2467_ = lean_ctor_get(v_kind_2466_, 0);
v_str_2468_ = lean_ctor_get(v_kind_2466_, 1);
if (lean_obj_tag(v_pre_2467_) == 1)
{
lean_object* v_pre_2474_; lean_object* v_str_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; 
v_pre_2474_ = lean_ctor_get(v_pre_2467_, 0);
v_str_2475_ = lean_ctor_get(v_pre_2467_, 1);
v___x_2476_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2477_ = lean_string_dec_eq(v_str_2475_, v___x_2476_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2479_ = lean_string_dec_eq(v_str_2468_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_box(0);
return v___x_2480_;
}
else
{
goto v___jp_2469_;
}
}
else
{
lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2481_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2482_ = lean_string_dec_eq(v_str_2468_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_box(0);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_box(v___x_2482_);
lean_inc(v_pre_2474_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_pre_2474_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
return v___x_2486_;
}
}
}
else
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2488_ = lean_string_dec_eq(v_str_2468_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
v___x_2489_ = lean_box(0);
return v___x_2489_;
}
else
{
goto v___jp_2469_;
}
}
v___jp_2469_:
{
uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2470_ = 0;
v___x_2471_ = lean_box(v___x_2470_);
lean_inc(v_pre_2467_);
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v_pre_2467_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
return v___x_2473_;
}
}
else
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_box(0);
return v___x_2490_;
}
}
else
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_box(0);
return v___x_2491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2492_);
lean_dec(v_x_2492_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2494_, size_t v_i_2495_, size_t v_stop_2496_, lean_object* v_b_2497_){
_start:
{
lean_object* v___y_2499_; uint8_t v___x_2503_; 
v___x_2503_ = lean_usize_dec_eq(v_i_2495_, v_stop_2496_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_array_uget_borrowed(v_as_2494_, v_i_2495_);
v___x_2505_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2504_);
if (lean_obj_tag(v___x_2505_) == 0)
{
v___y_2499_ = v_b_2497_;
goto v___jp_2498_;
}
else
{
lean_object* v_val_2506_; lean_object* v___x_2507_; 
v_val_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_val_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = lean_array_push(v_b_2497_, v_val_2506_);
v___y_2499_ = v___x_2507_;
goto v___jp_2498_;
}
}
else
{
return v_b_2497_;
}
v___jp_2498_:
{
size_t v___x_2500_; size_t v___x_2501_; 
v___x_2500_ = ((size_t)1ULL);
v___x_2501_ = lean_usize_add(v_i_2495_, v___x_2500_);
v_i_2495_ = v___x_2501_;
v_b_2497_ = v___y_2499_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2508_, lean_object* v_i_2509_, lean_object* v_stop_2510_, lean_object* v_b_2511_){
_start:
{
size_t v_i_boxed_2512_; size_t v_stop_boxed_2513_; lean_object* v_res_2514_; 
v_i_boxed_2512_ = lean_unbox_usize(v_i_2509_);
lean_dec(v_i_2509_);
v_stop_boxed_2513_ = lean_unbox_usize(v_stop_2510_);
lean_dec(v_stop_2510_);
v_res_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2508_, v_i_boxed_2512_, v_stop_boxed_2513_, v_b_2511_);
lean_dec_ref(v_as_2508_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2517_, lean_object* v_start_2518_, lean_object* v_stop_2519_){
_start:
{
lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2520_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2521_ = lean_nat_dec_lt(v_start_2518_, v_stop_2519_);
if (v___x_2521_ == 0)
{
return v___x_2520_;
}
else
{
lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = lean_array_get_size(v_as_2517_);
v___x_2523_ = lean_nat_dec_le(v_stop_2519_, v___x_2522_);
if (v___x_2523_ == 0)
{
uint8_t v___x_2524_; 
v___x_2524_ = lean_nat_dec_lt(v_start_2518_, v___x_2522_);
if (v___x_2524_ == 0)
{
return v___x_2520_;
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = lean_usize_of_nat(v_start_2518_);
v___x_2526_ = lean_usize_of_nat(v___x_2522_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2517_, v___x_2525_, v___x_2526_, v___x_2520_);
return v___x_2527_;
}
}
else
{
size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = lean_usize_of_nat(v_start_2518_);
v___x_2529_ = lean_usize_of_nat(v_stop_2519_);
v___x_2530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2517_, v___x_2528_, v___x_2529_, v___x_2520_);
return v___x_2530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2531_, lean_object* v_start_2532_, lean_object* v_stop_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2531_, v_start_2532_, v_stop_2533_);
lean_dec(v_stop_2533_);
lean_dec(v_start_2532_);
lean_dec_ref(v_as_2531_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2535_){
_start:
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2535_);
v___x_2537_ = l_Lean_Syntax_isOfKind(v_stx_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2535_);
lean_dec(v_stx_2535_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2539_; 
v___x_2539_ = lean_box(0);
return v___x_2539_;
}
else
{
lean_object* v_val_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_val_2540_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_val_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
return v___x_2542_;
}
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2543_ = l_Lean_Syntax_getArgs(v_stx_2535_);
lean_dec(v_stx_2535_);
v___x_2544_ = lean_unsigned_to_nat(0u);
v___x_2545_ = lean_array_get_size(v___x_2543_);
v___x_2546_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2543_, v___x_2544_, v___x_2545_);
lean_dec_ref(v___x_2543_);
v___x_2547_ = lean_array_to_list(v___x_2546_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2549_){
_start:
{
if (lean_obj_tag(v_x_2549_) == 1)
{
lean_object* v_kind_2550_; 
v_kind_2550_ = lean_ctor_get(v_x_2549_, 1);
if (lean_obj_tag(v_kind_2550_) == 1)
{
lean_object* v_pre_2551_; lean_object* v_str_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v_pre_2551_ = lean_ctor_get(v_kind_2550_, 0);
v_str_2552_ = lean_ctor_get(v_kind_2550_, 1);
v___x_2553_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2554_ = lean_string_dec_eq(v_str_2552_, v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_box(0);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; 
lean_inc(v_pre_2551_);
v___x_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_pre_2551_);
return v___x_2556_;
}
}
else
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_box(0);
return v___x_2557_;
}
}
else
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_box(0);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2559_);
lean_dec(v_x_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2561_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
uint8_t v___x_2563_; 
v___x_2563_ = 0;
return v___x_2563_;
}
else
{
uint8_t v___x_2564_; 
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = 1;
return v___x_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2565_){
_start:
{
uint8_t v_res_2566_; lean_object* v_r_2567_; 
v_res_2566_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2565_);
lean_dec(v_stx_2565_);
v_r_2567_ = lean_box(v_res_2566_);
return v_r_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_unsigned_to_nat(3u);
v___x_2570_ = l_Lean_Syntax_getArg(v_stx_2568_, v___x_2569_);
v___x_2571_ = l_Lean_Syntax_getArgs(v___x_2570_);
lean_dec(v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2572_);
lean_dec(v_stx_2572_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2574_){
_start:
{
uint8_t v___x_2575_; 
v___x_2575_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_unsigned_to_nat(1u);
v___x_2577_ = l_Lean_Syntax_getArg(v_stx_2574_, v___x_2576_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = lean_unsigned_to_nat(5u);
v___x_2579_ = l_Lean_Syntax_getArg(v_stx_2574_, v___x_2578_);
return v___x_2579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2580_);
lean_dec(v_stx_2580_);
return v_res_2581_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2587_ = l_Lean_mkAtom(v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2590_ = l_Lean_mkAtom(v___x_2589_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2591_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2592_ = lean_unsigned_to_nat(6u);
v___x_2593_ = lean_mk_empty_array_with_capacity(v___x_2592_);
v___x_2594_ = lean_array_push(v___x_2593_, v___x_2591_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2595_, lean_object* v_contents_2596_, lean_object* v_suffix_2597_, lean_object* v_nesting_2598_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_nesting_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2599_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2600_ = lean_mk_array(v_nesting_2598_, v___x_2599_);
v___x_2601_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2602_ = lean_box(2);
v_nesting_2603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2603_, 0, v___x_2602_);
lean_ctor_set(v_nesting_2603_, 1, v___x_2601_);
lean_ctor_set(v_nesting_2603_, 2, v___x_2600_);
v___x_2604_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2605_ = l_Lean_Name_append(v_kind_2595_, v___x_2604_);
v___x_2606_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2602_);
lean_ctor_set(v___x_2607_, 1, v___x_2601_);
lean_ctor_set(v___x_2607_, 2, v_contents_2596_);
v___x_2608_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2609_ = l_Lean_mkAtom(v_suffix_2597_);
v___x_2610_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2611_ = lean_array_push(v___x_2610_, v_nesting_2603_);
v___x_2612_ = lean_array_push(v___x_2611_, v___x_2606_);
v___x_2613_ = lean_array_push(v___x_2612_, v___x_2607_);
v___x_2614_ = lean_array_push(v___x_2613_, v___x_2608_);
v___x_2615_ = lean_array_push(v___x_2614_, v___x_2609_);
v___x_2616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2602_);
lean_ctor_set(v___x_2616_, 1, v___x_2605_);
lean_ctor_set(v___x_2616_, 2, v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2618_){
_start:
{
if (lean_obj_tag(v_x_2618_) == 1)
{
lean_object* v_kind_2619_; 
v_kind_2619_ = lean_ctor_get(v_x_2618_, 1);
if (lean_obj_tag(v_kind_2619_) == 1)
{
lean_object* v_pre_2620_; lean_object* v_str_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v_pre_2620_ = lean_ctor_get(v_kind_2619_, 0);
v_str_2621_ = lean_ctor_get(v_kind_2619_, 1);
v___x_2622_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2623_ = lean_string_dec_eq(v_str_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_box(0);
return v___x_2624_;
}
else
{
lean_object* v___x_2625_; 
lean_inc(v_pre_2620_);
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_pre_2620_);
return v___x_2625_;
}
}
else
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_box(0);
return v___x_2626_;
}
}
else
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_box(0);
return v___x_2627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2628_);
lean_dec(v_x_2628_);
return v_res_2629_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2630_);
if (lean_obj_tag(v___x_2631_) == 0)
{
uint8_t v___x_2632_; 
v___x_2632_ = 0;
return v___x_2632_;
}
else
{
uint8_t v___x_2633_; 
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = 1;
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2634_){
_start:
{
uint8_t v_res_2635_; lean_object* v_r_2636_; 
v_res_2635_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2634_);
lean_dec(v_stx_2634_);
v_r_2636_ = lean_box(v_res_2635_);
return v_r_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = l_Lean_Syntax_getArg(v_stx_2637_, v___x_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2640_);
lean_dec(v_stx_2640_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2644_, lean_object* v_inner_2645_, lean_object* v_suffix_2646_){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2647_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2648_ = l_Lean_Name_append(v_kind_2644_, v___x_2647_);
v___x_2649_ = l_Lean_mkAtom(v_suffix_2646_);
v___x_2650_ = lean_unsigned_to_nat(2u);
v___x_2651_ = lean_mk_empty_array_with_capacity(v___x_2650_);
v___x_2652_ = lean_array_push(v___x_2651_, v_inner_2645_);
v___x_2653_ = lean_array_push(v___x_2652_, v___x_2649_);
v___x_2654_ = lean_box(2);
v___x_2655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v___x_2648_);
lean_ctor_set(v___x_2655_, 2, v___x_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2659_){
_start:
{
lean_object* v___x_2660_; uint8_t v___x_2661_; 
v___x_2660_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2661_ = l_Lean_Syntax_isOfKind(v_stx_2659_, v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2662_){
_start:
{
uint8_t v_res_2663_; lean_object* v_r_2664_; 
v_res_2663_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2662_);
v_r_2664_ = lean_box(v_res_2663_);
return v_r_2664_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2665_){
_start:
{
uint8_t v___y_2667_; uint8_t v___x_2670_; 
v___x_2670_ = l_Lean_Syntax_isAntiquot(v_stx_2665_);
if (v___x_2670_ == 0)
{
uint8_t v___x_2671_; 
v___x_2671_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2665_);
v___y_2667_ = v___x_2671_;
goto v___jp_2666_;
}
else
{
v___y_2667_ = v___x_2670_;
goto v___jp_2666_;
}
v___jp_2666_:
{
if (v___y_2667_ == 0)
{
uint8_t v___x_2668_; 
v___x_2668_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2665_);
if (v___x_2668_ == 0)
{
uint8_t v___x_2669_; 
v___x_2669_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2665_);
return v___x_2669_;
}
else
{
lean_dec(v_stx_2665_);
return v___x_2668_;
}
}
else
{
lean_dec(v_stx_2665_);
return v___y_2667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2672_){
_start:
{
uint8_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2672_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2678_, lean_object* v_stx_2679_, lean_object* v_visit_2680_, lean_object* v_stack_2681_, lean_object* v_accept_2682_, lean_object* v_a_2683_, lean_object* v_b_2684_){
_start:
{
lean_object* v_a_2686_; uint8_t v___x_2690_; 
v___x_2690_ = lean_nat_dec_lt(v_a_2683_, v_upperBound_2678_);
if (v___x_2690_ == 0)
{
lean_dec(v_a_2683_);
lean_dec_ref(v_accept_2682_);
lean_dec(v_stack_2681_);
lean_dec_ref(v_visit_2680_);
lean_dec(v_stx_2679_);
lean_inc_ref(v_b_2684_);
return v_b_2684_;
}
else
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v___x_2691_ = lean_box(0);
v___x_2692_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2693_ = l_Lean_Syntax_getArg(v_stx_2679_, v_a_2683_);
lean_inc_ref(v_visit_2680_);
lean_inc(v___x_2693_);
v___x_2694_ = lean_apply_1(v_visit_2680_, v___x_2693_);
v___x_2695_ = lean_unbox(v___x_2694_);
if (v___x_2695_ == 0)
{
lean_dec(v___x_2693_);
v_a_2686_ = v___x_2692_;
goto v___jp_2685_;
}
else
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_inc(v_a_2683_);
lean_inc(v_stx_2679_);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_stx_2679_);
lean_ctor_set(v___x_2696_, 1, v_a_2683_);
lean_inc(v_stack_2681_);
v___x_2697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v_stack_2681_);
lean_inc_ref(v_accept_2682_);
lean_inc_ref(v_visit_2680_);
v___x_2698_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2680_, v_accept_2682_, v___x_2697_, v___x_2693_);
if (lean_obj_tag(v___x_2698_) == 1)
{
lean_object* v___x_2699_; lean_object* v___x_2700_; 
lean_dec(v_a_2683_);
lean_dec_ref(v_accept_2682_);
lean_dec(v_stack_2681_);
lean_dec_ref(v_visit_2680_);
lean_dec(v_stx_2679_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v___x_2691_);
return v___x_2700_;
}
else
{
lean_dec(v___x_2698_);
v_a_2686_ = v___x_2692_;
goto v___jp_2685_;
}
}
}
v___jp_2685_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_add(v_a_2683_, v___x_2687_);
lean_dec(v_a_2683_);
v_a_2683_ = v___x_2688_;
v_b_2684_ = v_a_2686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2701_, lean_object* v_accept_2702_, lean_object* v_stack_2703_, lean_object* v_stx_2704_){
_start:
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
lean_inc_ref(v_accept_2702_);
lean_inc(v_stx_2704_);
v___x_2705_ = lean_apply_1(v_accept_2702_, v_stx_2704_);
v___x_2706_ = lean_unbox(v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v_fst_2712_; 
v___x_2707_ = l_Lean_Syntax_getNumArgs(v_stx_2704_);
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_box(0);
v___x_2710_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2707_, v_stx_2704_, v_visit_2701_, v_stack_2703_, v_accept_2702_, v___x_2708_, v___x_2710_);
lean_dec(v___x_2707_);
v_fst_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_fst_2712_);
lean_dec_ref(v___x_2711_);
if (lean_obj_tag(v_fst_2712_) == 0)
{
return v___x_2709_;
}
else
{
lean_object* v_val_2713_; 
v_val_2713_ = lean_ctor_get(v_fst_2712_, 0);
lean_inc(v_val_2713_);
lean_dec_ref_known(v_fst_2712_, 1);
return v_val_2713_;
}
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec_ref(v_accept_2702_);
lean_dec_ref(v_visit_2701_);
v___x_2714_ = lean_unsigned_to_nat(0u);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_stx_2704_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v_stack_2703_);
v___x_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2718_, lean_object* v_stx_2719_, lean_object* v_visit_2720_, lean_object* v_stack_2721_, lean_object* v_accept_2722_, lean_object* v_a_2723_, lean_object* v_b_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2718_, v_stx_2719_, v_visit_2720_, v_stack_2721_, v_accept_2722_, v_a_2723_, v_b_2724_);
lean_dec_ref(v_b_2724_);
lean_dec(v_upperBound_2718_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2726_, lean_object* v_stx_2727_, lean_object* v_visit_2728_, lean_object* v_stack_2729_, lean_object* v_accept_2730_, lean_object* v_inst_2731_, lean_object* v_R_2732_, lean_object* v_a_2733_, lean_object* v_b_2734_, lean_object* v_c_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2726_, v_stx_2727_, v_visit_2728_, v_stack_2729_, v_accept_2730_, v_a_2733_, v_b_2734_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2737_, lean_object* v_stx_2738_, lean_object* v_visit_2739_, lean_object* v_stack_2740_, lean_object* v_accept_2741_, lean_object* v_inst_2742_, lean_object* v_R_2743_, lean_object* v_a_2744_, lean_object* v_b_2745_, lean_object* v_c_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2737_, v_stx_2738_, v_visit_2739_, v_stack_2740_, v_accept_2741_, v_inst_2742_, v_R_2743_, v_a_2744_, v_b_2745_, v_c_2746_);
lean_dec_ref(v_b_2745_);
lean_dec(v_upperBound_2737_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2748_, lean_object* v_visit_2749_, lean_object* v_accept_2750_){
_start:
{
lean_object* v___x_2751_; uint8_t v___x_2752_; 
lean_inc_ref(v_visit_2749_);
lean_inc(v_root_2748_);
v___x_2751_ = lean_apply_1(v_visit_2749_, v_root_2748_);
v___x_2752_ = lean_unbox(v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; 
lean_dec_ref(v_accept_2750_);
lean_dec_ref(v_visit_2749_);
lean_dec(v_root_2748_);
v___x_2753_ = lean_box(0);
return v___x_2753_;
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2749_, v_accept_2750_, v___x_2754_, v_root_2748_);
return v___x_2755_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2756_, lean_object* v_x_2757_, lean_object* v_p_2758_){
_start:
{
if (lean_obj_tag(v_p_2758_) == 0)
{
lean_dec_ref(v_x_2757_);
return v___x_2756_;
}
else
{
lean_object* v_fst_2759_; lean_object* v_val_2760_; uint8_t v___x_2761_; 
v_fst_2759_ = lean_ctor_get(v_x_2757_, 0);
lean_inc(v_fst_2759_);
lean_dec_ref(v_x_2757_);
v_val_2760_ = lean_ctor_get(v_p_2758_, 0);
v___x_2761_ = l_Lean_Syntax_isOfKind(v_fst_2759_, v_val_2760_);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2762_, lean_object* v_x_2763_, lean_object* v_p_2764_){
_start:
{
uint8_t v___x_121__boxed_2765_; uint8_t v_res_2766_; lean_object* v_r_2767_; 
v___x_121__boxed_2765_ = lean_unbox(v___x_2762_);
v_res_2766_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_121__boxed_2765_, v_x_2763_, v_p_2764_);
lean_dec(v_p_2764_);
v_r_2767_ = lean_box(v_res_2766_);
return v_r_2767_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2768_){
_start:
{
if (lean_obj_tag(v_x_2768_) == 0)
{
uint8_t v___x_2769_; 
v___x_2769_ = 1;
return v___x_2769_;
}
else
{
lean_object* v_head_2770_; uint8_t v___x_2771_; 
v_head_2770_ = lean_ctor_get(v_x_2768_, 0);
v___x_2771_ = lean_unbox(v_head_2770_);
if (v___x_2771_ == 0)
{
uint8_t v___x_2772_; 
v___x_2772_ = lean_unbox(v_head_2770_);
return v___x_2772_;
}
else
{
lean_object* v_tail_2773_; 
v_tail_2773_ = lean_ctor_get(v_x_2768_, 1);
v_x_2768_ = v_tail_2773_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2775_){
_start:
{
uint8_t v_res_2776_; lean_object* v_r_2777_; 
v_res_2776_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2775_);
lean_dec(v_x_2775_);
v_r_2777_ = lean_box(v_res_2776_);
return v_r_2777_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2780_, lean_object* v_pattern_2781_){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = l_List_lengthTR___redArg(v_pattern_2781_);
v___x_2783_ = l_List_lengthTR___redArg(v_stack_2780_);
v___x_2784_ = lean_nat_dec_le(v___x_2782_, v___x_2783_);
lean_dec(v___x_2783_);
lean_dec(v___x_2782_);
if (v___x_2784_ == 0)
{
lean_dec(v_pattern_2781_);
lean_dec(v_stack_2780_);
return v___x_2784_;
}
else
{
lean_object* v___x_2785_; lean_object* v___f_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2785_ = lean_box(v___x_2784_);
v___f_2786_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2786_, 0, v___x_2785_);
v___x_2787_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2788_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2786_, v_stack_2780_, v_pattern_2781_, v___x_2787_);
v___x_2789_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2788_);
lean_dec(v___x_2788_);
return v___x_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2790_, lean_object* v_pattern_2791_){
_start:
{
uint8_t v_res_2792_; lean_object* v_r_2793_; 
v_res_2792_ = l_Lean_Syntax_Stack_matches(v_stack_2790_, v_pattern_2791_);
v_r_2793_ = lean_box(v_res_2792_);
return v_r_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2794_, lean_object* v_trailing_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2794_);
if (lean_obj_tag(v___x_2796_) == 1)
{
lean_object* v_val_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2832_; 
v_val_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2832_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_val_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2832_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
if (lean_obj_tag(v_val_2797_) == 0)
{
lean_object* v_trailing_2801_; lean_object* v_leading_2802_; lean_object* v_pos_2803_; lean_object* v_endPos_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2830_; 
v_trailing_2801_ = lean_ctor_get(v_val_2797_, 2);
v_leading_2802_ = lean_ctor_get(v_val_2797_, 0);
v_pos_2803_ = lean_ctor_get(v_val_2797_, 1);
v_endPos_2804_ = lean_ctor_get(v_val_2797_, 3);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_val_2797_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2806_ = v_val_2797_;
v_isShared_2807_ = v_isSharedCheck_2830_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_endPos_2804_);
lean_inc(v_trailing_2801_);
lean_inc(v_pos_2803_);
lean_inc(v_leading_2802_);
lean_dec(v_val_2797_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2830_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v_str_2808_; lean_object* v_startPos_2809_; lean_object* v_stopPos_2810_; lean_object* v_startPos_2811_; lean_object* v_stopPos_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2828_; 
v_str_2808_ = lean_ctor_get(v_trailing_2801_, 0);
lean_inc_ref(v_str_2808_);
v_startPos_2809_ = lean_ctor_get(v_trailing_2801_, 1);
lean_inc(v_startPos_2809_);
v_stopPos_2810_ = lean_ctor_get(v_trailing_2801_, 2);
lean_inc(v_stopPos_2810_);
lean_dec_ref(v_trailing_2801_);
v_startPos_2811_ = lean_ctor_get(v_trailing_2795_, 1);
v_stopPos_2812_ = lean_ctor_get(v_trailing_2795_, 2);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_trailing_2795_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v_trailing_2795_, 0);
lean_dec(v_unused_2829_);
v___x_2814_ = v_trailing_2795_;
v_isShared_2815_ = v_isSharedCheck_2828_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_stopPos_2812_);
lean_inc(v_startPos_2811_);
lean_dec(v_trailing_2795_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2828_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
uint8_t v_decide_2816_; 
v_decide_2816_ = lean_nat_dec_eq(v_stopPos_2810_, v_startPos_2811_);
lean_dec(v_startPos_2811_);
lean_dec(v_stopPos_2810_);
if (v_decide_2816_ == 0)
{
lean_object* v___x_2817_; 
lean_del_object(v___x_2814_);
lean_dec(v_stopPos_2812_);
lean_dec(v_startPos_2809_);
lean_dec_ref(v_str_2808_);
lean_del_object(v___x_2806_);
lean_dec(v_endPos_2804_);
lean_dec(v_pos_2803_);
lean_dec_ref(v_leading_2802_);
lean_del_object(v___x_2799_);
lean_dec(v_stx_2794_);
v___x_2817_ = lean_box(0);
return v___x_2817_;
}
else
{
lean_object* v_trailing_2819_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 1, v_startPos_2809_);
lean_ctor_set(v___x_2814_, 0, v_str_2808_);
v_trailing_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_str_2808_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_startPos_2809_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_stopPos_2812_);
v_trailing_2819_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2821_; 
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 2, v_trailing_2819_);
v___x_2821_ = v___x_2806_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_leading_2802_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_pos_2803_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_trailing_2819_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_endPos_2804_);
v___x_2821_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = l_Lean_Syntax_setTailInfo(v_stx_2794_, v___x_2821_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2822_);
v___x_2824_ = v___x_2799_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2831_; 
lean_del_object(v___x_2799_);
lean_dec(v_val_2797_);
lean_dec_ref(v_trailing_2795_);
lean_dec(v_stx_2794_);
v___x_2831_ = lean_box(0);
return v___x_2831_;
}
}
}
else
{
lean_object* v___x_2833_; 
lean_dec(v___x_2796_);
lean_dec_ref(v_trailing_2795_);
lean_dec(v_stx_2794_);
v___x_2833_ = lean_box(0);
return v___x_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2834_, lean_object* v_trailing_2835_){
_start:
{
lean_object* v___x_2836_; 
lean_inc(v_stx_2834_);
v___x_2836_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2834_, v_trailing_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
return v_stx_2834_;
}
else
{
lean_object* v_val_2837_; 
lean_dec(v_stx_2834_);
v_val_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v___x_2836_, 1);
return v_val_2837_;
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
